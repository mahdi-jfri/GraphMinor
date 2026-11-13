module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section5ReductionSize
import GraphMinor.GM06.Section5Reduction4Progress
import GraphMinor.GM06.Section5ReductionTheta
import GraphMinor.GM06.Section5Equivalence

/-!
# The reduction history and measure for VI (5.7)

Our proof of (5.7) (outlined in `Alg57Algorithm.lean`) keeps a bit after every reduction. Reductions
1–3 set it to one. Reduction 4 sets it to zero and enables an earlier
reduction. Therefore two successive rounds cannot both use Reduction
4. Each round decreases twice the ordinary vertex-plus-edge count
plus the bit.

The history below records actual admissible reductions and their
bit updates. Its invariant preserves the given winding and the next
feasibility question. Counting the bit changes pairs each Reduction
4 with a size-decreasing round when the final bit is one. This proves
the bound of twice the initial size in Lemma 19. These
are properties of actual reduction histories, before their connection
to the RAM loop of VI (5.7), page 133.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The mathematical pair and the single control bit at a loop entry. -/
structure Alg57DrawingState (k : ℕ) where
  drawing : Drawing ClosedCylinder
  linkage : CylinderLinkage k drawing
  bit : Bool

namespace Alg57DrawingState

/-- The ordinary size used in the paper's reduction induction. -/
@[expose] noncomputable def size {k : ℕ} (X : Alg57DrawingState k) : ℕ :=
  X.drawing.V.ncard + X.drawing.E.ncard

/-- Lemma 19's integer measure `M = 2μ+b`. -/
@[expose] noncomputable def measure {k : ℕ} (X : Alg57DrawingState k) : ℕ := 2 * X.size + X.bit.toNat

end Alg57DrawingState

/-- A recorded round contains its actual admissible reduction and
literal bit update. The Boolean index is true precisely for Reduction
4, whose branch is reached with the bit one. -/
inductive Alg57ReductionRound {k : ℕ} : Alg57DrawingState k → Alg57DrawingState k → Bool → Prop
  | one {X Y} (step : Section5Reduction1Step k X.drawing X.linkage Y.drawing Y.linkage)
      (proper : IsCylinderSection5Drawing k Y.drawing) (bit : Y.bit = true) :
      Alg57ReductionRound X Y false
  | two {X Y} (step : Section5Reduction2Step k X.drawing X.linkage Y.drawing Y.linkage)
      (proper : IsCylinderSection5Drawing k Y.drawing) (bit : Y.bit = true) :
      Alg57ReductionRound X Y false
  | three {X Y} (step : Section5Reduction3Step k X.drawing X.linkage Y.drawing Y.linkage)
      (proper : IsCylinderSection5Drawing k Y.drawing) (bit : Y.bit = true) :
      Alg57ReductionRound X Y false
  | four {X Y} (step : Section5Reduction4Step k X.drawing X.linkage Y.drawing Y.linkage)
      (proper : IsCylinderSection5Drawing k Y.drawing)
      (oldBit : X.bit = true) (newBit : Y.bit = false) : Alg57ReductionRound X Y true

namespace Alg57ReductionRound
variable {k : ℕ} {X Y Z : Alg57DrawingState k} {b : Bool}

/-- Every recorded transition is an actual Section 5 reduction. -/
theorem reduction (h : Alg57ReductionRound X Y b) :
    Section5ReductionStep k X.drawing X.linkage Y.drawing Y.linkage := by
  cases h with
  | one h _ _ => exact Or.inl h
  | two h _ _ => exact Or.inr (Or.inl h)
  | three h _ _ => exact Or.inr (Or.inr (Or.inl h))
  | four h _ _ _ => exact Or.inr (Or.inr (Or.inr h))

/-- Every next drawing is proper, as required of a valid reduction. -/
theorem proper (h : Alg57ReductionRound X Y b) : IsCylinderSection5Drawing k Y.drawing := by
  cases h <;> assumption

/-- The recorded output bit distinguishes the two types of round. -/
theorem bit_eq_not (h : Alg57ReductionRound X Y b) : Y.bit = !b := by
  cases h <;> assumption

/-- The bit updates count at most one rerouting per size-decreasing
round, with the current bit as the unpaired credit. -/
theorem bit_credit (h : Alg57ReductionRound X Y b) :
    b.toNat + Y.bit.toNat ≤ (!b).toNat + X.bit.toNat := by
  cases h with
  | one _ _ hb | two _ _ hb | three _ _ hb =>
    simp only [hb, Bool.toNat_false, Bool.toNat_true, Bool.not_false]
    omega
  | four _ _ hx hy => simp [hx, hy]

/-- Each ordinary round removes at least one unit of size, and a
rerouting leaves the ordinary drawing unchanged. -/
theorem size_credit (h : Alg57ReductionRound X Y b) :
    Y.size + (!b).toNat ≤ X.size := by
  cases h with
  | one hr _ _ =>
    have hh := drawing_size_lt_of_reduction1 hr
    change Y.size < X.size at hh
    simp only [Bool.not_false, Bool.toNat_true]
    omega
  | two hr _ _ =>
    have hh := drawing_size_lt_of_reduction2 hr
    change Y.size < X.size at hh
    simp only [Bool.not_false, Bool.toNat_true]
    omega
  | three hr _ _ =>
    have hh := drawing_size_lt_of_reduction3 hr
    change Y.size < X.size at hh
    simp only [Bool.not_false, Bool.toNat_true]
    omega
  | four hr _ _ _ => simp only [Alg57DrawingState.size, hr.1, Bool.not_true, Bool.toNat_false, Nat.add_zero, le_refl]

/-- Every performed round strictly decreases `2μ+b`, including a
size-decreasing round whose incoming bit was zero. -/
theorem measure_lt (h : Alg57ReductionRound X Y b) : Y.measure < X.measure := by
  have hs := h.size_credit
  have hb := h.bit_credit
  cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true] at hs hb
  · have hxy : X.bit.toNat ≤ 1 := by cases X.bit <;> decide
    have hyy : Y.bit.toNat ≤ 1 := by cases Y.bit <;> decide
    unfold Alg57DrawingState.measure
    omega
  · unfold Alg57DrawingState.measure
    omega

/-- A rerouting cannot be followed by a second rerouting: its output
bit is zero, whereas the next rerouting branch requires one. -/
theorem no_consecutive_four (h : Alg57ReductionRound X Y true)
    (h' : Alg57ReductionRound Y Z true) : False := by
  have hy : Y.bit = false := h.bit_eq_not
  cases h' with
  | four _ _ hone _ => exact Bool.false_ne_true (hy.symm.trans hone)

/-- If a performed round leaves bit zero, a proper Reduction 1, 2
or 3 is available. This is the fifth invariant of Lemma 18. -/
theorem early_reduction_of_zero_bit (h : Alg57ReductionRound X Y b)
    (hX : IsCylinderSection5Drawing k X.drawing) (hy : Y.bit = false) :
    ∃ (G : Drawing ClosedCylinder) (L : CylinderLinkage k G),
      IsCylinderSection5Drawing k G ∧
        (Section5Reduction1Step k Y.drawing Y.linkage G L ∨
          Section5Reduction2Step k Y.drawing Y.linkage G L ∨
            Section5Reduction3Step k Y.drawing Y.linkage G L) := by
  cases h with
  | one _ _ hone | two _ _ hone | three _ _ hone =>
    exact False.elim (Bool.false_ne_true (hy.symm.trans hone))
  | four hr _ _ _ => exact reduction123_applies_after_reduction4 X.linkage Y.linkage hX hr

/-- A recorded admissible round preserves the actual reference
winding, using the proved winding preservation of all four reductions. -/
theorem hasTheta (h : Alg57ReductionRound X Y b)
    (hX : IsCylinderSection5Drawing k X.drawing) {θ : ℝ} (hθ : X.linkage.HasTheta θ) :
    Y.linkage.HasTheta θ := by
  obtain ⟨φ, hφ⟩ := CylinderLinkage.exists_hasTheta h.proper.1 Y.linkage
  have he := theta_eq_of_reduction k X.drawing Y.drawing X.linkage Y.linkage
    θ φ hX.1 hθ hφ h.reduction
  exact he ▸ hφ

/-- The exact next-feasibility question is unchanged in one round,
by the proved VI (5.6), rather than an assumed reduction property. -/
theorem next_feasible_iff (h : Alg57ReductionRound X Y b)
    (hX : IsCylinderSection5Drawing k X.drawing) {θ : ℝ} (hθ : X.linkage.HasTheta θ) :
    IsThetaFeasible k Y.drawing (θ + 1 / (k : ℝ)) ↔
      IsThetaFeasible k X.drawing (θ + 1 / (k : ℝ)) :=
  theorem_5_6_proof k X.drawing Y.drawing X.linkage Y.linkage θ θ hX h.proper
    hθ (h.hasTheta hX hθ) h.reduction

end Alg57ReductionRound

/-- An actual reduction history, indexed separately by its count
of size-decreasing rounds and its count of rerouting rounds. -/
inductive Alg57ReductionRun {k : ℕ} :
    Alg57DrawingState k → Alg57DrawingState k → ℕ → ℕ → Prop
  | nil (X) : Alg57ReductionRun X X 0 0
  | shrink {X Y Z d r} (step : Alg57ReductionRound X Y false)
      (rest : Alg57ReductionRun Y Z d r) : Alg57ReductionRun X Z (d + 1) r
  | reroute {X Y Z d r} (step : Alg57ReductionRound X Y true)
      (rest : Alg57ReductionRun Y Z d r) : Alg57ReductionRun X Z d (r + 1)

namespace Alg57ReductionRun
variable {k : ℕ} {X Y : Alg57DrawingState k} {d r : ℕ}

/-- Joining actual chronological reduction histories adds their
counts of shrinking and rerouting rounds separately. -/
theorem append {Z : Alg57DrawingState k} {e q : ℕ}
    (h : Alg57ReductionRun X Y d r) (h' : Alg57ReductionRun Y Z e q) :
    Alg57ReductionRun X Z (d + e) (r + q) := by
  induction h with
  | nil => simpa only [Nat.zero_add] using h'
  | shrink step rest ih =>
    simpa only [Nat.add_right_comm] using Alg57ReductionRun.shrink step (ih h')
  | reroute step rest ih =>
    simpa only [Nat.add_right_comm] using Alg57ReductionRun.reroute step (ih h')

/-- Appending one actual size-decreasing RAM branch extends the
mathematical history by exactly one shrinking round. -/
theorem snoc_shrink {Z : Alg57DrawingState k} (h : Alg57ReductionRun X Y d r)
    (step : Alg57ReductionRound Y Z false) : Alg57ReductionRun X Z (d + 1) r := by
  simpa only [Nat.zero_add, Nat.add_zero] using h.append (.shrink step (.nil Z))

/-- Appending one actual rerouting extends the mathematical history
by exactly one rerouting round. -/
theorem snoc_reroute {Z : Alg57DrawingState k} (h : Alg57ReductionRun X Y d r)
    (step : Alg57ReductionRound Y Z true) : Alg57ReductionRun X Z d (r + 1) := by
  simpa only [Nat.zero_add, Nat.add_zero] using h.append (.reroute step (.nil Z))

/-- Only size-decreasing rounds are charged against the initial
ordinary vertex and edge count. -/
theorem size_bound (h : Alg57ReductionRun X Y d r) : Y.size + d ≤ X.size := by
  induction h with
  | nil => omega
  | shrink step _ ih =>
    have hs := step.size_credit
    simp only [Bool.not_false, Bool.toNat_true] at hs
    omega
  | reroute step _ ih =>
    have hs := step.size_credit
    simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at hs
    omega

/-- The bit supplies the credit for an unmatched rerouting. With
both endpoint bits one, every rerouting is paired with a later
size-decreasing round. -/
theorem reroute_bound (h : Alg57ReductionRun X Y d r) :
    r + Y.bit.toNat ≤ d + X.bit.toNat := by
  induction h with
  | nil => omega
  | shrink step _ ih =>
    have hb := step.bit_credit
    simp only [Bool.not_false, Bool.toNat_true, Bool.toNat_false, Nat.zero_add] at hb
    omega
  | reroute step _ ih =>
    have hb := step.bit_credit
    simp only [Bool.not_true, Bool.toNat_false, Bool.toNat_true, Nat.zero_add] at hb
    omega

/-- The total number of recorded rounds is at most the decrease
in the integer measure of Lemma 19. -/
theorem rounds_add_measure_le (h : Alg57ReductionRun X Y d r) :
    Y.measure + d + r ≤ X.measure := by
  induction h with
  | nil => omega
  | shrink step _ ih => have hh := step.measure_lt; omega
  | reroute step _ ih => have hh := step.measure_lt; omega

/-- Lemma 19 of our proof of (5.7): at most twice the initial
ordinary size reduction rounds precede a terminal state with bit one. -/
theorem rounds_le_twice_size (h : Alg57ReductionRun X Y d r)
    (hx : X.bit = true) (hy : Y.bit = true) : d + r ≤ 2 * X.size := by
  have hs := h.size_bound
  have hr := h.reroute_bound
  simp only [hx, hy, Bool.toNat_true] at hr
  omega

/-- The first four mathematical invariants of Lemma 18 hold along
the actual history: the final drawing is proper, its winding is
unchanged, and next feasibility is equivalent to that of the input. -/
theorem invariant (h : Alg57ReductionRun X Y d r)
    (hX : IsCylinderSection5Drawing k X.drawing) {θ : ℝ} (hθ : X.linkage.HasTheta θ) :
    IsCylinderSection5Drawing k Y.drawing ∧ Y.linkage.HasTheta θ ∧
      (IsThetaFeasible k Y.drawing (θ + 1 / (k : ℝ)) ↔
        IsThetaFeasible k X.drawing (θ + 1 / (k : ℝ))) := by
  induction h with
  | nil => exact ⟨hX, hθ, Iff.rfl⟩
  | shrink step _ ih | reroute step _ ih =>
    obtain ⟨hY, hθY, heq⟩ := ih step.proper (step.hasTheta hX hθ)
    exact ⟨hY, hθY, heq.trans (step.next_feasible_iff hX hθ)⟩

/-- The zero-bit invariant passes through every recorded round.
The initial implication is vacuous when the initialization sets bit one. -/
theorem early_reduction_of_zero_bit (h : Alg57ReductionRun X Y d r)
    (hX : IsCylinderSection5Drawing k X.drawing)
    (hinit : X.bit = false →
      ∃ (G : Drawing ClosedCylinder) (L : CylinderLinkage k G),
        IsCylinderSection5Drawing k G ∧
          (Section5Reduction1Step k X.drawing X.linkage G L ∨
            Section5Reduction2Step k X.drawing X.linkage G L ∨
              Section5Reduction3Step k X.drawing X.linkage G L))
    (hy : Y.bit = false) :
    ∃ (G : Drawing ClosedCylinder) (L : CylinderLinkage k G),
      IsCylinderSection5Drawing k G ∧
        (Section5Reduction1Step k Y.drawing Y.linkage G L ∨
          Section5Reduction2Step k Y.drawing Y.linkage G L ∨
            Section5Reduction3Step k Y.drawing Y.linkage G L) := by
  induction h with
  | nil => exact hinit hy
  | shrink step _ ih | reroute step _ ih =>
    exact ih step.proper (step.early_reduction_of_zero_bit hX) hy

/-- Failure of just the first three scans forces bit one, before
the rerouting phase is called. A zero bit would supply an earlier
reduction by the proved fifth invariant of Lemma 18. -/
theorem bit_eq_true_of_no_early (h : Alg57ReductionRun X Y d r)
    (hX : IsCylinderSection5Drawing k X.drawing) (hx : X.bit = true)
    (hstop : ∀ (G : Drawing ClosedCylinder) (L : CylinderLinkage k G),
      ¬ Section5Reduction1Step k Y.drawing Y.linkage G L ∧
      ¬ Section5Reduction2Step k Y.drawing Y.linkage G L ∧
      ¬ Section5Reduction3Step k Y.drawing Y.linkage G L) : Y.bit = true := by
  cases hy : Y.bit with
  | true => rfl
  | false =>
    obtain ⟨G, L, _, hr⟩ := h.early_reduction_of_zero_bit hX
      (fun hzero => False.elim (Bool.false_ne_true (hzero.symm.trans hx))) hy
    have hn := hstop G L
    rcases hr with h1 | h2 | h3
    · exact False.elim (hn.1 h1)
    · exact False.elim (hn.2.1 h2)
    · exact False.elim (hn.2.2 h3)

/-- Once all reduction scans fail, the control bit is one. A zero
bit would supply an actual earlier reduction by the proved invariant. -/
theorem terminal_bit_eq_true (h : Alg57ReductionRun X Y d r)
    (hX : IsCylinderSection5Drawing k X.drawing) (hx : X.bit = true)
    (hstop : ¬ Section5AnyReductionApplies k Y.drawing Y.linkage) : Y.bit = true := by
  cases hy : Y.bit with
  | true => rfl
  | false =>
    obtain ⟨G, L, hG, hr⟩ := h.early_reduction_of_zero_bit hX
      (fun hzero => False.elim (Bool.false_ne_true (hzero.symm.trans hx))) hy
    apply False.elim
    apply hstop
    refine ⟨G, L, hG, ?_⟩
    rcases hr with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))

/-- The full round-count assertion of Lemma 19: a history initialized
with bit one reaches its terminal test after at most twice the input
ordinary size reductions. The terminal test itself is one further round. -/
theorem rounds_le_twice_size_at_terminal (h : Alg57ReductionRun X Y d r)
    (hX : IsCylinderSection5Drawing k X.drawing) (hx : X.bit = true)
    (hstop : ¬ Section5AnyReductionApplies k Y.drawing Y.linkage) :
    d + r ≤ 2 * X.size ∧ d + r + 1 ≤ 2 * X.size + 1 := by
  have hh := h.rounds_le_twice_size hx (h.terminal_bit_eq_true hX hx hstop)
  exact ⟨hh, Nat.add_le_add_right hh 1⟩

end Alg57ReductionRun
end GraphMinor.GM06
