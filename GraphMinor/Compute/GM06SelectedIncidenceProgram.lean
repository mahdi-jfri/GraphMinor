module

public import GraphMinor.Compute.GM06SelectedFaceProgram
public import GraphMinor.Compute.GM06IncidenceProgram

/-!
# Computing the selected face and both incidence tables

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) runs
FACE_ROWS on a cut component, selects the reverse inner cuff face and marks
its vertex and edge incidence. This program performs all three
operations from component rotations, active ends and origins. It
saves the vertex count while FACE_ROWS uses the dart count, then
restores it for incidence marking. The selected row and both tables
are returned together, including a precise absent-face result.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Save vertex count, construct and select faces, then tabulate incidence. -/
def gm06SelectedIncidenceProg : Cmd :=
  .seq (.assign 669 (.reg 648))
    (.seq (.assign 648 (.op .mul (.const 2) (.reg 649)))
      (.seq gm06SelectedFaceProg
        (.seq (gm13TabulateProg 650 (.len 626) (.read 626 (.reg 650)) 601)
          (.seq (.assign 648 (.reg 669)) gm06FaceIncidenceProg))))

/-- The selected row and its computed vertex/edge incidence tables. -/
def gm06SelectedIncidenceResult (s : State) : Option (List ℕ × List ℕ × List ℕ) :=
  if s.regs 668 = 0 then none else some (s.arrs 600, s.arrs 606, s.arrs 607)

/-- Registers changed by complete face selection and incidence marking. -/
def gm06SelectedIncidenceRegs : List ℕ := [648, 669] ++ gm06SelectedFaceRegs ++ [650, 610, 611, 612]

private theorem incidence_result_of_selection {n m : ℕ} (origins : List ℕ)
    (choice : Option (List (Fin (2 * m)))) (s : State)
    (hs : gm06SelectFaceRowResult s = choice.map (List.map Fin.val))
    (hv : s.arrs 606 = gm06IncV n origins ((choice.getD []).map Fin.val))
    (he : s.arrs 607 = gm06IncE m ((choice.getD []).map Fin.val)) :
    gm06SelectedIncidenceResult s = choice.map (fun row =>
      (row.map Fin.val, gm06IncV n origins (row.map Fin.val), gm06IncE m (row.map Fin.val))) := by
  cases choice with
  | none =>
    have hz : s.regs 668 = 0 := by
      by_cases hz : s.regs 668 = 0
      · exact hz
      · simp only [gm06SelectFaceRowResult, hz, ↓reduceIte, Option.map_none, reduceCtorEq] at hs
    simp only [gm06SelectedIncidenceResult, hz, ↓reduceIte, Option.map_none]
  | some row =>
    have hz : s.regs 668 ≠ 0 := by
      intro hz
      simp only [gm06SelectFaceRowResult, hz, ↓reduceIte, Option.map_some, reduceCtorEq] at hs
    have hrow : s.arrs 600 = row.map Fin.val := by
      simpa only [gm06SelectFaceRowResult, hz, ↓reduceIte, Option.map_some, Option.some.injEq] using hs
    simp only [gm06SelectedIncidenceResult, hz, ↓reduceIte, hrow, hv, he, Option.getD_some, Option.map_some]

/-- Exact selected face, IncV and IncE from the component's finite
rotation system. The only supplied tables are original endpoint data. -/
theorem gm06SelectedIncidenceProg_exec {w n m : ℕ} (origin : Fin (2 * m) → Fin n)
    (rotations : List (List (Fin (2 * m)))) (active : List (Fin (2 * m)))
    (reverseInner : Fin (2 * m)) (s : State)
    (hnd : rotations.flatten.Nodup) (hcover : ∀ d, d ∈ active ↔ d ∈ rotations.flatten)
    (hmate : ∀ d ∈ active, gm06DartReversal m d ∈ active)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hcap : 1 + 2 * (2 * m) < 2 ^ w)
    (hcode : (gm06EncodeRows (rotations.map (List.map Fin.val))).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows (rotations.map (List.map Fin.val)), x < 2 ^ w)
    (hl : active.length < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows (rotations.map (List.map Fin.val)))
    (h604 : s.arrs 604 = active.map Fin.val)
    (h626 : s.arrs 626 = List.ofFn (fun d => (origin d).val))
    (h648 : s.regs 648 = n) (h649 : s.regs 649 = m) (h667 : s.regs 667 = reverseInner.val) :
    ∃ sf t, Exec w gm06SelectedIncidenceProg s sf t ∧
      t ≤ 164 + n + m + 221 * (2 * m) + 29 * rotations.length + 37 * rotations.flatten.length +
        active.length * (40 + 18 * (2 * m)) ∧
      Keeps gm06SelectedIncidenceRegs [600, 601, 602, 603, 604, 605, 606, 607] s sf ∧
      gm06SelectedIncidenceResult sf = gm06SelectedFaceIncidence n
        (List.ofFn (fun d => (origin d).val)) rotations active reverseInner := by
  have hw1 : 1 < 2 ^ w := by omega
  have hq : 2 * m < 2 ^ w := by omega
  let choice := gm06SelectedFace rotations active reverseInner
  let row := choice.getD []
  have hrowLen : row.length ≤ 2 * m := by
    cases hs : gm06SelectedFace rotations active reverseInner with
    | none => simp only [row, choice, hs, Option.getD_none, List.length_nil]; omega
    | some r =>
      have hm := gm06SelectFaceRow_some (gm06ActiveFaceRows rotations active) reverseInner r hs
      have hndRow := (gm06ActiveFaceRows_spec rotations active hnd hcover hmate).1.sublist (List.sublist_flatten_of_mem hm.1)
      simpa only [row, choice, hs, Option.getD_some, Fintype.card_fin] using hndRow.length_le_card
  have hrowMap : (choice.map (List.map Fin.val)).getD [] = row.map Fin.val := by
    dsimp only [row]
    cases choice <;> rfl
  let s₀ := s.setReg 669 n
  let s₁ := s₀.setReg 648 (2 * m)
  have he₀ : Exec w (.assign 669 (.reg 648)) s s₀ 2 := .assign (GraphMinor.Compute.Crossing.eval_reg h648 hn)
  have he₁ : Exec w (.assign 648 (.op .mul (.const 2) (.reg 649))) s₀ s₁ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₀] using h649) (by omega)) hq)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hs₂, hr₂⟩ := gm06SelectedFaceProg_exec rotations active reverseInner s₁
    hnd hcover hmate hw hcap hcode hwords hl h600 h604 (by simp [s₁]) (by simpa [s₁, s₀] using h667)
  have h600₂ : s₂.arrs 600 = row.map Fin.val := hr₂.trans hrowMap
  have h626₂ : s₂.arrs 626 = List.ofFn (fun d => (origin d).val) := (hk₂.2 626 (by decide)).trans h626
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm13TabulateProg_exec
    650 (.len 626) (.read 626 (.reg 650)) 601 (List.ofFn (fun d => (origin d).val)) s₂ hw1 (by simpa using hq)
    (fun z hk => by
      simpa only [List.length_ofFn] using (GraphMinor.Compute.Crossing.eval_len
        ((hk.2 626 (by decide)).trans h626₂) (by simpa using hq)))
    (fun z i hi hk hr => by
      have horg := (hk.2 626 (by decide)).trans h626₂
      have hiq : i < 2 * m := by simpa only [List.length_ofFn] using hi
      have hread := GraphMinor.Compute.Crossing.eval_read (w := w) (a := 626)
        (GraphMinor.Compute.Crossing.eval_reg hr (hiq.trans hq)) (by simpa only [horg, List.length_ofFn] using hiq)
        (by simpa only [horg, List.getElem_ofFn] using (origin ⟨i, hiq⟩).isLt.trans hn)
      simpa only [horg] using hread)
  let s₄ := s₃.setReg 648 n
  have h669 : s₃.regs 669 = n := (hk₃.1 669 (by decide)).trans
    ((hk₂.1 669 (by simp [gm06SelectedFaceRegs, gm06FaceRowsRegs, gm06PredecessorRegs])).trans (by simp [s₁, s₀]))
  have he₄ : Exec w (.assign 648 (.reg 669)) s₃ s₄ 2 := .assign (GraphMinor.Compute.Crossing.eval_reg h669 hn)
  obtain ⟨sf, tf, hef, htf, hkf, hvf, hefTable⟩ := gm06FaceIncidenceProg_exec origin row s₄ hw hn hq
    (hrowLen.trans_lt hq) ((hk₃.2 600 (by decide)).trans h600₂) hd₃ (by simp [s₄])
    ((hk₃.1 649 (by decide)).trans ((hk₂.1 649 (by simp [gm06SelectedFaceRegs, gm06FaceRowsRegs, gm06PredecessorRegs])).trans h649))
  have hk₀₂ : Keeps gm06SelectedIncidenceRegs [600, 601, 602, 603, 604, 605, 606, 607] s s₂ :=
    ((((Keeps.refl _ _ s).setReg (by simp [gm06SelectedIncidenceRegs]) _).setReg
      (by simp [gm06SelectedIncidenceRegs]) _).trans hk₂
        (by intro r hr; simp [gm06SelectedIncidenceRegs, hr]) (by simp))
  have hk₂f : Keeps gm06SelectedIncidenceRegs [600, 601, 602, 603, 604, 605, 606, 607] s₂ sf :=
    ((hk₃.mono (by simp [gm06SelectedIncidenceRegs]) (by simp)).setReg
      (by simp [gm06SelectedIncidenceRegs]) _).trans hkf (by simp [gm06SelectedIncidenceRegs]) (by simp)
  have hsFinal : gm06SelectFaceRowResult sf = choice.map (List.map Fin.val) := by
    have h668 : sf.regs 668 = s₂.regs 668 := (hkf.1 668 (by decide)).trans
      (by simpa [s₄] using hk₃.1 668 (by decide))
    have h600f : sf.arrs 600 = s₂.arrs 600 := (hkf.2 600 (by decide)).trans (hk₃.2 600 (by decide))
    simpa only [gm06SelectFaceRowResult, h668, h600f] using hs₂
  refine ⟨sf, 2 + (4 + (t₂ + (t₃ + (2 + tf)))), .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef)))), ?_,
    hk₀₂.trans hk₂f (fun _ h => h) (fun _ h => h), incidence_result_of_selection _ choice sf hsFinal hvf hefTable⟩
  simp only [Expr.cost, List.length_ofFn] at ht₃
  omega

/-- Uniform quadratic bound for full selected-face incidence construction. -/
theorem gm06SelectedIncidence_cost_le_polynomial (n m r d a : ℕ) :
    164 + n + m + 221 * (2 * m) + 29 * r + 37 * d + a * (40 + 18 * (2 * m)) ≤
      1000 * (n + 2 * m + r + d + a + 1) ^ 2 := by
  let N := n + 2 * m + r + d + a + 1
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hbase : 2 * m + r + d + a + 1 ≤ N := by dsimp only [N]; omega
  have hsquare : (2 * m + r + d + a + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hbase 2
  have hface := (gm06SelectedFace_cost_le_polynomial (2 * m) r d a).trans (Nat.mul_le_mul_left 500 hsquare)
  have hlinear : 46 + n + m + 73 * (2 * m) ≤ 200 * N := by dsimp only [N]; omega
  have hNN : N ≤ N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hN
  change _ ≤ 1000 * N ^ 2
  rw [pow_two] at hface ⊢
  omega

end GraphMinor.Compute
