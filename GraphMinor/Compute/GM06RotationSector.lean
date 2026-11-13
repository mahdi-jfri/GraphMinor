module

public import GraphMinor.Compute.GM06FindLabel
public import GraphMinor.Compute.GM06Alg34Between

/-!
# A directed sector query in a rotation row

Three directed labels are supplied in registers 36, 37 and 38. Find
their positions in the rotation row, then test whether the third lies
strictly between the first two in cyclic order. Directed labels keep
the two ends of a loop distinct. This finite sector query is a building
block for the side conditions in the cylinder reductions.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Return the cyclic-sector flag in 43 for directed labels in registers 36--38. -/
def gm06RotationSectorProg (rot : Arr) : Cmd :=
  .seq (gm06FindLabelProg rot 36 50 40)
    (.seq (gm06FindLabelProg rot 37 50 41)
      (.seq (gm06FindLabelProg rot 38 50 42) (gm06BetweenProg 43 40 41 42)))

/-- The directed sector query computes the cyclic-order flag in linear time. -/
theorem gm06RotationSectorProg_exec {w : ℕ} (rot : ℕ) (xs : List ℕ)
    (p q r : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (hr : r ∈ xs)
    (ha : s.arrs rot = xs) (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) (h38 : s.regs 38 = r) :
    ∃ s' t, Exec w (gm06RotationSectorProg rot) s s' t ∧
      t ≤ 34 + 39 * xs.length ∧ Keeps [50, 40, 41, 42, 43] [] s s' ∧
      s'.regs 43 = (if GM06DrawingData.cyclicBetween
        (xs.idxOf p) (xs.idxOf q) (xs.idxOf r) then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hi₁⟩ := gm06FindLabelProg_exec_nodup rot 36 50 40
    (by decide) (by decide) (by decide) xs p s hw1 hn hx hnd hp ha h36
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hi₂⟩ := gm06FindLabelProg_exec_nodup rot 37 50 41
    (by decide) (by decide) (by decide) xs q s₁ hw1 hn hx hnd hq
    ((hk₁.2 rot (by simp)).trans ha) ((hk₁.1 37 (by decide)).trans h37)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hi₃⟩ := gm06FindLabelProg_exec_nodup rot 38 50 42
    (by decide) (by decide) (by decide) xs r s₂ hw1 hn hx hnd hr
    ((hk₂.2 rot (by simp)).trans ((hk₁.2 rot (by simp)).trans ha))
    ((hk₂.1 38 (by decide)).trans ((hk₁.1 38 (by decide)).trans h38))
  have hip : s₃.regs 40 = xs.idxOf p :=
    (hk₃.1 40 (by decide)).trans ((hk₂.1 40 (by decide)).trans hi₁)
  have hiq : s₃.regs 41 = xs.idxOf q := (hk₃.1 41 (by decide)).trans hi₂
  obtain ⟨t₄, he₄, ht₄⟩ := gm06BetweenProg_exec 43 40 41 42 (s := s₃) hw
    (by rw [hip]; exact (List.idxOf_lt_length_of_mem hp).trans hn)
    (by rw [hiq]; exact (List.idxOf_lt_length_of_mem hq).trans hn)
    (by rw [hi₃]; exact (List.idxOf_lt_length_of_mem hr).trans hn)
  rw [hip, hiq, hi₃] at he₄
  let s₄ := s₃.setReg 43 (if GM06DrawingData.cyclicBetween
    (xs.idxOf p) (xs.idxOf q) (xs.idxOf r) then 1 else 0)
  have he : Exec w (gm06RotationSectorProg rot) s s₄ (t₁ + (t₂ + (t₃ + t₄))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  refine ⟨s₄, _, he, by omega, ⟨?_, ?_⟩, by simp [s₄]⟩
  · intro j hj
    apply he.regs_eq_of_not_mem_writtenRegs
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp only [gm06RotationSectorProg, gm06FindLabelProg, gm06BetweenProg, forUp,
      Cmd.writtenRegs, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
      or_false, not_or]
    tauto
  · intro a _
    apply he.arrs_eq_of_not_mem_writtenArrs
    simp [gm06RotationSectorProg, gm06FindLabelProg, gm06BetweenProg, forUp, Cmd.writtenArrs]

end GraphMinor.Compute
