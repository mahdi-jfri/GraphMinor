module

public import GraphMinor.Compute.GM06Alg511BinaryLoop
public import GraphMinor.GM06.Alg511PositiveDrawingInput
public import GraphMinor.GM06.Alg511RoundBound
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# The binary feasibility-loop invariant

A live round retains an actual encoded linkage, whose winding is
the initial winding plus one over k for each successful call. Its
binary current value increases by the fixed positive increment.
A stopped state either retains a linkage at the target or records
the proved negative answer. All branches retain the supplied graph
fields, binary row formats and graph-count scalar words.

These are predicates on reached machine states, not extra input
objects. The call bound from VI (5.12) rules out a live state at the
end of the controller's 1+|V(G)|/k rounds. Thus a verified run of
this invariant yields exactly the decision required by VI (5.11),
page 134, with an encoded linkage on a positive answer.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface

/-- A signed row has one actual sign bit and binary magnitude
digits, with the stated bound on its supplied width. -/
def alg511BinaryRowFormat (row : List ℕ) (width : ℕ) : Prop :=
  ∃ sign digits, row = sign :: digits ∧ sign < 2 ∧ digits.length ≤ width ∧ ∀ d ∈ digits, d < 2

/-- Increasing a row-width allowance retains its same supplied bits. -/
theorem alg511BinaryRowFormat.mono {row : List ℕ} {a b : ℕ}
    (h : alg511BinaryRowFormat row a) (hab : a ≤ b) : alg511BinaryRowFormat row b := by
  obtain ⟨sign, digits, hrow, hs, hlen, hbits⟩ := h
  exact ⟨sign, digits, hrow, hs, hlen.trans hab, hbits⟩

/-- Every encoded sign/digit word is a bit and the complete row
has at most one more word than the allowed magnitude width. -/
theorem alg511BinaryRowFormat.words {row : List ℕ} {width : ℕ}
    (h : alg511BinaryRowFormat row width) : row.length ≤ width + 1 ∧ ∀ d ∈ row, d < 2 := by
  obtain ⟨sign, digits, rfl, hs, hlen, hbits⟩ := h
  refine ⟨by simp only [List.length_cons]; omega, ?_⟩
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hs
  · exact hbits d hd

/-- The five original drawing fields retained by the packed call. -/
def alg511BinaryLoopTables (x : GM06Alg511WindingInput) (s : State) : Prop :=
  s.arrs 1500 = [x.drawing.vertexCount] ∧ s.arrs 1230 = x.drawing.endpoints ∧
    s.arrs 1231 = gm06EncodeRows x.drawing.rotations ∧
    s.arrs 1210 = x.drawing.innerCuff ∧ s.arrs 1211 = x.drawing.outerCuff

/-- Preserving the five actual field arrays preserves their supplied
interpretation, independently of every scratch register and array. -/
theorem alg511BinaryLoopTables.frame {x : GM06Alg511WindingInput} {s t : State}
    (h : alg511BinaryLoopTables x s)
    (ha : ∀ a ∈ gm06Alg511RetainedSuccessorArrays, t.arrs a = s.arrs a) :
    alg511BinaryLoopTables x t := by
  exact ⟨(ha 1500 (by decide)).trans h.1, (ha 1230 (by decide)).trans h.2.1,
    (ha 1231 (by decide)).trans h.2.2.1, (ha 1210 (by decide)).trans h.2.2.2.1,
    (ha 1211 (by decide)).trans h.2.2.2.2⟩

/-- The data common to live and stopped states of controller round i.
The metadata row is used only to preserve the ordinary loop counter.
The counter can lag by one while a successful body updates its linkage. -/
def alg511BinaryLoopCommon (x : GM06Alg511WindingInput) (target increment : List ℕ)
    (base i : ℕ) (s : State) : Prop :=
  s.regs 6002 ≤ i ∧ s.regs 52 = x.drawing.pathCount ∧
    (∀ r ∈ ([54, 55, 62, 63, 66] : List ℕ), s.regs r = 0) ∧
    alg511BinaryLoopTables x s ∧ s.arrs 2801 = target ∧ s.arrs 2802 = increment ∧
    (s.arrs 2803).length = 1 ∧ alg511BinaryRowFormat (s.arrs 2800) (base + i)

/-- Common data transfer through a concrete transition. Only the
current row format, metadata length and counter need fresh proofs. -/
theorem alg511BinaryLoopCommon.update {x : GM06Alg511WindingInput} {target increment : List ℕ}
    {base i j : ℕ} {s t : State} (h : alg511BinaryLoopCommon x target increment base i s)
    (hr : ∀ r ∈ ([54, 55, 62, 63, 66, 52] : List ℕ), t.regs r = s.regs r)
    (ha : ∀ a ∈ gm06Alg511RetainedSuccessorArrays ++ [2801, 2802], t.arrs a = s.arrs a)
    (hcounter : t.regs 6002 ≤ j) (hmeta : (t.arrs 2803).length = 1)
    (hformat : alg511BinaryRowFormat (t.arrs 2800) (base + j)) :
    alg511BinaryLoopCommon x target increment base j t := by
  obtain ⟨_, hk, hz, ht, htarget, hincrement, _, _⟩ := h
  refine ⟨hcounter, (hr 52 (by decide)).trans hk, ?_, ?_,
    (ha 2801 (by decide)).trans htarget, (ha 2802 (by decide)).trans hincrement, hmeta, hformat⟩
  · intro r hmem
    exact (hr r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢; tauto)).trans (hz r hmem)
  · exact ht.frame (fun a hm => ha a (List.mem_append.mpr (Or.inl hm)))

/-- Attaching the retained current path rows gives the six actual
source fields expected by the successor packer. -/
theorem alg511BinaryLoopCommon.fields {x : GM06Alg511WindingInput} {target increment : List ℕ}
    {base i : ℕ} {s : State} (h : alg511BinaryLoopCommon x target increment base i s)
    (rows : List (List ℕ)) (hp : s.arrs 8 = gm06EncodeRows rows) :
    ∀ j : Fin 6, s.arrs (gm06Alg511SuccessorFieldSources j) =
      (gm06SuccessorRows (x.drawing.withLinkage rows))[j.val]'(by simp [gm06SuccessorRows]) := by
  obtain ⟨_, _, _, ht, _, _, _, _⟩ := h
  intro j
  fin_cases j
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2.1
  · exact ht.2.2.2.1
  · exact ht.2.2.2.2
  · exact hp

/-- The seven saved scalar slots contain only initialized zeros,
the graph path count and the Boolean continuing bit. -/
theorem alg511BinaryLoopCommon.scalar_words {x : GM06Alg511WindingInput} {target increment : List ℕ}
    {base i w : ℕ} {s : State} (h : alg511BinaryLoopCommon x target increment base i s)
    (hw : 1 < 2 ^ w) (hk : x.drawing.pathCount < 2 ^ w) (hf : s.regs 6000 < 2) :
    ∀ r ∈ ([54, 55, 62, 63, 52, 66, 6000] : List ℕ), s.regs r < 2 ^ w := by
  obtain ⟨_, hK, hz, _, _, _, _, _⟩ := h
  have hzero (r : ℕ) (hr : r ∈ ([54, 55, 62, 63, 66] : List ℕ)) : s.regs r < 2 ^ w := by
    rw [hz r hr]
    exact Nat.two_pow_pos w
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hzero 54 (by decide)
  · exact hzero 55 (by decide)
  · exact hzero 62 (by decide)
  · exact hzero 63 (by decide)
  · simpa only [hK] using hk
  · exact hzero 66 (by decide)
  · exact hf.trans_le (by omega)

/-- Retained binary rows fit from their supplied digit widths and
the call cap. No interpreted magnitude enters this word bound. -/
theorem alg511BinaryLoopCommon.binary_words {x : GM06Alg511WindingInput} {target increment : List ℕ}
    {base i cap targetWidth incrementWidth w : ℕ} {s : State}
    (h : alg511BinaryLoopCommon x target increment base i s) (hi : i ≤ cap)
    (htarget : alg511BinaryRowFormat target targetWidth) (hincrement : alg511BinaryRowFormat increment incrementWidth)
    (hw : 1 < 2 ^ w) (hsize : max base (max targetWidth incrementWidth) + cap + 2 < 2 ^ w) :
    ∀ a ∈ ([2800, 2801, 2802] : List ℕ), (s.arrs a).length < 2 ^ w ∧ ∀ d ∈ s.arrs a, d < 2 ^ w := by
  obtain ⟨_, _, _, _, ht, he, _, hc⟩ := h
  have hcurrent := hc.words
  have htwords := htarget.words
  have hewords := hincrement.words
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨by omega, fun d hd => (hcurrent.2 d hd).trans_le (by omega)⟩
  · rw [ht]
    exact ⟨by omega, fun d hd => (htwords.2 d hd).trans_le (by omega)⟩
  · rw [he]
    exact ⟨by omega, fun d hd => (hewords.2 d hd).trans_le (by omega)⟩

/-- Adding the same positive integer increment at each successful
call makes signed binary comparison exactly comparison of rounds. -/
theorem alg511_binary_round_value_lt (number : ℤ) {increment i steps : ℕ} (hinc : 0 < increment) :
    number + (i : ℤ) * increment < number + (steps : ℤ) * increment ↔ i < steps := by
  have hd : (0 : ℤ) < increment := Int.natCast_pos.mpr hinc
  constructor
  · intro h
    have hi : (i : ℤ) < steps := by nlinarith only [h, hd]
    exact_mod_cast hi
  · intro h
    have hi : (i : ℤ) < steps := by exact_mod_cast h
    nlinarith only [hi, hd]

/-- The actual ordinary paths retained at a given winding increment. -/
def alg511BinaryLoopLinkage {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (start : ℝ) (i : ℕ) (s : State) : Prop :=
  ∃ (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ)),
    s.arrs 8 = gm06EncodeRows rows ∧
    GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels
      rep.graphTurn.graph.edgeLabels rows ∧ L.HasTheta (start + (i : ℝ) / x.drawing.pathCount)

/-- The linkage predicate depends only on the exact returned path
array, so arithmetic workspace changes retain the same linkage. -/
theorem alg511BinaryLoopLinkage.frame {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    {rep : GM06Alg511PositiveDrawingRep x G} {start : ℝ} {i : ℕ} {s t : State}
    (h : alg511BinaryLoopLinkage rep start i s) (ha : t.arrs 8 = s.arrs 8) :
    alg511BinaryLoopLinkage rep start i t := by
  obtain ⟨L, rows, hrows, henc, htheta⟩ := h
  exact ⟨L, rows, ha.trans hrows, henc, htheta⟩

/-- The retained actual linkage proves feasibility at this round. -/
theorem alg511BinaryLoopLinkage.feasible {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    {rep : GM06Alg511PositiveDrawingRep x G} {start : ℝ} {i : ℕ} {s : State}
    (h : alg511BinaryLoopLinkage rep start i s) :
    IsThetaFeasible x.drawing.pathCount G (start + (i : ℝ) / x.drawing.pathCount) := by
  obtain ⟨L, _, _, _, htheta⟩ := h
  exact ⟨L, htheta⟩

/-- The live branch has exactly i successful calls and is still
below the target step. Its next value is obtained by binary addition. -/
def alg511BinaryLoopRunning {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (start : ℝ) (number : ℤ)
    (increment steps i : ℕ) (s : State) : Prop :=
  s.regs 6000 = 1 ∧ s.regs 6001 = 1 ∧ i < steps ∧
    gm06Alg511BinaryRowValue (s.arrs 2800) = number + (i : ℤ) * increment ∧
    alg511BinaryLoopLinkage rep start i s

/-- A stopped controller branch has either the proved negative
answer or a retained actual linkage at the target step. -/
def alg511BinaryLoopFinished {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (start : ℝ) (steps : ℕ) (s : State) : Prop :=
  (s.regs 6000 = 0 ∧ s.regs 6001 = 0 ∧
    ¬ IsThetaFeasible x.drawing.pathCount G (start + (steps : ℝ) / x.drawing.pathCount)) ∨
  (s.regs 6000 = 1 ∧ s.regs 6001 = 0 ∧ alg511BinaryLoopLinkage rep start steps s)

/-- The full reached-state invariant for the binary controller.
Its two terminal branches record conclusions only after a proved
transition reaches them. They are not conditions on supplied input. -/
def alg511BinaryLoopState {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (target incrementRow : List ℕ)
    (base : ℕ) (start : ℝ) (number : ℤ) (increment steps i : ℕ) (s : State) : Prop :=
  alg511BinaryLoopCommon x target incrementRow base i s ∧
    (alg511BinaryLoopRunning rep start number increment steps i s ∨ alg511BinaryLoopFinished rep start steps s)

/-- A stopped branch is retained when only its counter or
arithmetic scratch changes, with its bit and path array preserved. -/
theorem alg511BinaryLoopFinished.frame {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    {rep : GM06Alg511PositiveDrawingRep x G} {start : ℝ} {steps : ℕ} {s t : State}
    (h : alg511BinaryLoopFinished rep start steps s)
    (hf : t.regs 6000 = s.regs 6000) (hg : t.regs 6001 = s.regs 6001) (ha : t.arrs 8 = s.arrs 8) :
    alg511BinaryLoopFinished rep start steps t := by
  rcases h with h | h
  · exact Or.inl ⟨hf.trans h.1, hg.trans h.2.1, h.2.2⟩
  · exact Or.inr ⟨hf.trans h.1, hg.trans h.2.1, h.2.2.frame ha⟩

/-- Preserving the flags, current value and path row preserves a
live state, independently of arithmetic scratch and the counter. -/
theorem alg511BinaryLoopRunning.frame {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    {rep : GM06Alg511PositiveDrawingRep x G} {start : ℝ} {number : ℤ}
    {increment steps i : ℕ} {s t : State}
    (h : alg511BinaryLoopRunning rep start number increment steps i s)
    (hf : t.regs 6000 = s.regs 6000) (hg : t.regs 6001 = s.regs 6001)
    (hv : t.arrs 2800 = s.arrs 2800) (hp : t.arrs 8 = s.arrs 8) :
    alg511BinaryLoopRunning rep start number increment steps i t := by
  exact ⟨hf.trans h.1, hg.trans h.2.1, h.2.2.1,
    (congrArg gm06Alg511BinaryRowValue hv).trans h.2.2.2.1, h.2.2.2.2.frame hp⟩

/-- Updating the ordinary counter within the logical round bound
retains the whole state invariant. In particular this justifies the
controller increment after a successful body. -/
theorem alg511BinaryLoopState.setCounter {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    {rep : GM06Alg511PositiveDrawingRep x G} {target incrementRow : List ℕ}
    {base : ℕ} {start : ℝ} {number : ℤ} {increment steps i counter : ℕ} {s : State}
    (h : alg511BinaryLoopState rep target incrementRow base start number increment steps i s)
    (hc : counter ≤ i) :
    alg511BinaryLoopState rep target incrementRow base start number increment steps i (s.setReg 6002 counter) := by
  refine ⟨alg511BinaryLoopCommon.update h.1 ?_ (fun _ _ => rfl) ?_ h.1.2.2.2.2.2.2.1 h.1.2.2.2.2.2.2.2, ?_⟩
  · intro r hr
    apply State.setReg_regs_ne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simpa only [State.setReg_regs_self] using hc
  · rcases h.2 with hr | hf
    · exact Or.inl (hr.frame (State.setReg_regs_ne _ _ (by decide))
        (State.setReg_regs_ne _ _ (by decide)) rfl rfl)
    · exact Or.inr (hf.frame (State.setReg_regs_ne _ _ (by decide))
        (State.setReg_regs_ne _ _ (by decide)) rfl)

/-- Every reached branch has Boolean continuing and guard words. -/
theorem alg511BinaryLoopState.bits {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    {rep : GM06Alg511PositiveDrawingRep x G} {target incrementRow : List ℕ}
    {base : ℕ} {start : ℝ} {number : ℤ} {increment steps i : ℕ} {s : State}
    (h : alg511BinaryLoopState rep target incrementRow base start number increment steps i s) :
    s.regs 6000 < 2 ∧ s.regs 6001 < 2 := by
  rcases h.2 with h | h
  · rw [h.1, h.2.1]; exact ⟨by decide, by decide⟩
  · rcases h with h | h <;> rw [h.1, h.2.1] <;> exact ⟨by decide, by decide⟩

/-- The vertex-label bijection equates the supplied vertex count
with the actual drawing's vertex cardinality. -/
theorem alg511_binary_vertexCount_eq_ncard {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) : x.drawing.vertexCount = G.V.ncard := by
  have h := Nat.card_congr rep.graphTurn.graph.vertex
  change Nat.card (Fin x.drawing.vertexCount) = Nat.card G.V at h
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using h

/-- By VI (5.12), a live state cannot remain after the cap
1+|V(G)|/k. This is the controller's exact call bound. -/
theorem alg511_binary_finished_at_cap {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (hG : IsCylinderSection5Drawing x.drawing.pathCount G)
    {start : ℝ} (hstart : IsThetaFeasible x.drawing.pathCount G start)
    {number : ℤ} {increment steps : ℕ} {s : State}
    (h : alg511BinaryLoopRunning rep start number increment steps
      (1 + x.drawing.vertexCount / x.drawing.pathCount) s ∨ alg511BinaryLoopFinished rep start steps s) :
    alg511BinaryLoopFinished rep start steps s := by
  rcases h with h | h
  · have hc := alg511_calls_le hG hstart h.2.2.2.2.feasible
    rw [alg511_binary_vertexCount_eq_ncard rep] at hc
    omega
  · exact h

/-- A stopped controller's bit gives the exact feasibility answer.
Its positive branch also retains an actual encoded target linkage. -/
theorem alg511BinaryLoopFinished.correct {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    {rep : GM06Alg511PositiveDrawingRep x G} {start : ℝ} {steps : ℕ} {s : State}
    (h : alg511BinaryLoopFinished rep start steps s) :
    s.regs 6000 < 2 ∧
      (s.regs 6000 = 1 ↔ IsThetaFeasible x.drawing.pathCount G (start + (steps : ℝ) / x.drawing.pathCount)) ∧
      (s.regs 6000 = 1 → alg511BinaryLoopLinkage rep start steps s) := by
  rcases h with h | h
  · refine ⟨by rw [h.1]; decide, ?_, ?_⟩
    · simp only [h.1, Nat.zero_ne_one, h.2.2]
    · intro he; rw [h.1] at he; exact (Nat.zero_ne_one he).elim
  · exact ⟨by rw [h.1]; decide, by simp only [h.1, h.2.2.feasible], fun _ => h.2.2⟩

end GraphMinor.GM06
