module

public import GraphMinor.Compute.GM06RotationSector

/-!
# Sector tests for a possibly absent directed end

An edge has two directed ends, and a chosen end need not occur in the
rotation at the queried vertex. Search for it first. If it is absent,
return zero. Otherwise apply the cyclic-sector query. This guard keeps
an absent end out of a sector that wraps around the list boundary.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The finite sector flag, with absent directed labels excluded. -/
def gm06RotationSectorFlag (xs : List ℕ) (p q r : ℕ) : ℕ :=
  if r ∈ xs then if GM06DrawingData.cyclicBetween
    (xs.idxOf p) (xs.idxOf q) (xs.idxOf r) then 1 else 0 else 0

/-- Every sector flag is at most one. -/
theorem gm06RotationSectorFlag_le_one (xs : List ℕ) (p q r : ℕ) :
    gm06RotationSectorFlag xs p q r ≤ 1 := by
  unfold gm06RotationSectorFlag
  split
  · split <;> omega
  · omega

/-- A sector flag is one exactly for a present label in the strict cyclic sector. -/
theorem gm06RotationSectorFlag_eq_one (xs : List ℕ) (p q r : ℕ) :
    gm06RotationSectorFlag xs p q r = 1 ↔ r ∈ xs ∧
      GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf r) = true := by
  unfold gm06RotationSectorFlag
  by_cases hm : r ∈ xs
  · simp only [hm, ite_true, true_and]
    cases h : GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf r) <;> simp [h]
  · simp [hm]

/-- Test the directed label in 38 only if it occurs in the rotation row. -/
def gm06OptionalRotationSectorProg (rot : Arr) : Cmd :=
  .seq (gm06FindLabelProg rot 38 50 42)
    (.ite (.op .lt (.reg 42) (.len rot))
      (gm06RotationSectorProg rot) (.assign 43 (.const 0)))

/-- A possibly absent directed end has the correct guarded sector flag. -/
theorem gm06OptionalRotationSectorProg_exec {w : ℕ} (rot : ℕ) (xs : List ℕ)
    (p q r : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (hrw : r < 2 ^ w)
    (ha : s.arrs rot = xs) (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) (h38 : s.regs 38 = r) :
    ∃ s' t, Exec w (gm06OptionalRotationSectorProg rot) s s' t ∧
      t ≤ 44 + 52 * xs.length ∧ Keeps [50, 40, 41, 42, 43] [] s s' ∧
      s'.regs 43 = (if r ∈ xs then if GM06DrawingData.cyclicBetween
        (xs.idxOf p) (xs.idxOf q) (xs.idxOf r) then 1 else 0 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd⟩ := gm06FindLabelProg_exec rot 38 50 42
    (by decide) (by decide) (by decide) xs r s hw1 hn hx hrw ha h38
  have hpos : s₁.regs 42 ≤ xs.length := by
    rcases hd with h | ⟨j, hj, hjr, _⟩
    · exact h.1.le
    · rw [hjr]; exact hj.le
  have hmem : s₁.regs 42 < xs.length ↔ r ∈ xs := by
    rcases hd with h | ⟨j, hj, hjr, hjv⟩
    · constructor
      · intro hh; rw [h.1] at hh; exact False.elim (Nat.lt_irrefl _ hh)
      · intro hm
        obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
        exact False.elim (h.2 j hj heq)
    · constructor
      · intro _; exact hjv ▸ List.getElem_mem hj
      · intro _; simpa only [hjr] using hj
  have hk₁' : Keeps [50, 40, 41, 42, 43] [] s s₁ := hk₁.mono (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> simp) (by simp)
  have hc := GraphMinor.Compute.Crossing.eval_lt
    (GraphMinor.Compute.Crossing.eval_reg rfl (hpos.trans_lt hn))
    (GraphMinor.Compute.Crossing.eval_len ((hk₁.2 rot (by simp)).trans ha) hn) hw1
  by_cases hm : r ∈ xs
  · obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hf⟩ := gm06RotationSectorProg_exec rot xs p q r s₁
      hw hn hx hnd hp hq hm ((hk₁.2 rot (by simp)).trans ha)
      ((hk₁.1 36 (by decide)).trans h36) ((hk₁.1 37 (by decide)).trans h37)
      ((hk₁.1 38 (by decide)).trans h38)
    have htest : s₁.regs 42 < xs.length := hmem.mpr hm
    refine ⟨s₂, t₁ + (3 + t₂), .seq he₁
      (.ite_true (by simpa only [htest, ite_true] using hc) (by decide) he₂),
      by omega, hk₁'.trans hk₂ (by simp) (by simp), ?_⟩
    simpa only [hm, ite_true] using hf
  · have htest : ¬s₁.regs 42 < xs.length := fun h => hm (hmem.mp h)
    let s₂ := s₁.setReg 43 0
    have he₂ : Exec w (.assign 43 (.const 0)) s₁ s₂ 2 :=
      .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    refine ⟨s₂, t₁ + 5, .seq he₁
      (.ite_false (by simpa only [htest, ite_false] using hc) he₂), by omega,
      hk₁'.setReg (by simp) _, ?_⟩
    simp [s₂, hm]

end GraphMinor.Compute
