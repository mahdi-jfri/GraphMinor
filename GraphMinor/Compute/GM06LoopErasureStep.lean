module

public import GraphMinor.Compute.GM06LoopErasurePop
import GraphMinor.Compute.CrossingOpsBasic

/-!
# One chronological loop-erasure iteration

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) reads the
next dart's head and its current stack position. An absent head is pushed.
A repeated head triggers the verified pop loop. The execution theorem
identifies this actual step with the pure chronological update. Its
amortized inequality charges popped darts to the earlier pushes.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the next dart and head, inspect its position and update both stacks. -/
def gm06EraseStepProg : Cmd :=
  .seq (.assign 611 (.read 603 (.reg 610)))
    (.seq (.assign 612 (.read 601 (.reg 611)))
      (.seq (.assign 613 (.read 606 (.reg 612)))
        (.ite (exprEq (.reg 613) (.reg 616)) gm06ErasePushProg gm06ErasePopLoop)))

/-- One actual iteration is the exact pure update. Its amortized bound
pays for every removed stack dart, without assuming a pop-count result. -/
theorem gm06EraseStepProg_exec {w n source i : ℕ} (heads input stack : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hfit : input.length + 2 < 2 ^ w)
    (hheadsFit : heads.length < 2 ^ w) (hi : i < input.length)
    (hinput : ∀ d ∈ input, d < heads.length) (hheads : ∀ v ∈ heads, v < n)
    (hroom : stack.length < input.length)
    (hnd : (gm06WalkVertices (fun d => heads[d]?.getD 0) source stack).Nodup)
    (hvertices : ∀ v ∈ gm06WalkVertices (fun d => heads[d]?.getD 0) source stack, v < n)
    (hstackWords : ∀ d ∈ stack, d < 2 ^ w)
    (h604 : IsStack 604 614 (input.length + 1) (gm06WalkVertices (fun d => heads[d]?.getD 0) source stack) s)
    (h605 : IsStack 605 615 input.length stack s)
    (h606 : s.arrs 606 = gm06StackPositions n (input.length + 1)
      (gm06WalkVertices (fun d => heads[d]?.getD 0) source stack))
    (h601 : s.arrs 601 = heads) (h603 : s.arrs 603 = input)
    (h610 : s.regs 610 = i) (h616 : s.regs 616 = input.length + 1) :
    let next := gm06EraseClosedStep (fun d => heads[d]?.getD 0) source stack input[i]
    ∃ sf t, Exec w gm06EraseStepProg s sf t ∧ t + 22 * next.length ≤ 60 + 22 * stack.length ∧
      Keeps [611, 612, 613, 615, 614, 617, 618] [605, 604, 606] s sf ∧
      IsStack 604 614 (input.length + 1) (gm06WalkVertices (fun d => heads[d]?.getD 0) source next) sf ∧
      IsStack 605 615 input.length next sf ∧
      sf.arrs 606 = gm06StackPositions n (input.length + 1)
        (gm06WalkVertices (fun d => heads[d]?.getD 0) source next) := by
  let head : ℕ → ℕ := fun d => heads[d]?.getD 0
  let vertices := gm06WalkVertices head source stack
  let d := input[i]
  let v := head d
  let position := if v ∈ vertices then vertices.idxOf v else input.length + 1
  let next := gm06EraseClosedStep head source stack d
  change ∃ sf t, Exec w gm06EraseStepProg s sf t ∧ t + 22 * next.length ≤ 60 + 22 * stack.length ∧
    Keeps [611, 612, 613, 615, 614, 617, 618] [605, 604, 606] s sf ∧
    IsStack 604 614 (input.length + 1) (gm06WalkVertices head source next) sf ∧
    IsStack 605 615 input.length next sf ∧
    sf.arrs 606 = gm06StackPositions n (input.length + 1) (gm06WalkVertices head source next)
  have hd : d < heads.length := hinput _ (List.getElem_mem hi)
  have hv : v < n := by
    simpa only [v, head, List.getElem?_eq_getElem hd, Option.getD_some] using hheads _ (List.getElem_mem hd)
  have hvLen : vertices.length = stack.length + 1 := by
    simp only [vertices, gm06WalkVertices, List.length_cons, List.length_map]
  have hposition : position < 2 ^ w := by
    dsimp only [position]
    split_ifs with hmem
    · have hidx := List.idxOf_lt_length_of_mem hmem
      omega
    · omega
  let s₁ := s.setReg 611 d
  let s₂ := s₁.setReg 612 v
  let s₃ := s₂.setReg 613 position
  have he₁ : Exec w (.assign 611 (.read 603 (.reg 610))) s s₁ 3 := by
    apply Exec.assign
    have he := GraphMinor.Compute.Crossing.eval_read (a := 603)
      (GraphMinor.Compute.Crossing.eval_reg (w := w) h610 (by omega))
      (by simpa only [h603] using hi) (by simpa only [h603] using hd.trans hheadsFit)
    simpa only [h603] using he
  have he₂ : Exec w (.assign 612 (.read 601 (.reg 611))) s₁ s₂ 3 := by
    apply Exec.assign
    have he := GraphMinor.Compute.Crossing.eval_read (w := w) (s := s₁) (a := 601)
      (GraphMinor.Compute.Crossing.eval_reg (r := 611) (by simp [s₁]) (hd.trans hheadsFit))
      (by simpa only [s₁, State.setReg_arrs, h601] using hd)
      (by simpa only [s₁, State.setReg_arrs, h601, v, head, List.getElem?_eq_getElem hd, Option.getD_some] using hv.trans hn)
    simpa only [s₁, State.setReg_arrs, h601, v, head, List.getElem?_eq_getElem hd, Option.getD_some] using he
  have hpos₂ : s₂.arrs 606 = gm06StackPositions n (input.length + 1) vertices := h606
  have hiPos : v < (s₂.arrs 606).length := by simpa only [hpos₂, gm06StackPositions_length] using hv
  have hget : (s₂.arrs 606)[v]'hiPos = position := by
    have he := gm06StackPositions_get (absent := input.length + 1) vertices hv
    rw [List.getElem?_eq_getElem (by simpa only [gm06StackPositions_length] using hv)] at he
    simpa only [hpos₂, Option.getD_some] using he
  have he₃ : Exec w (.assign 613 (.read 606 (.reg 612))) s₂ s₃ 3 := by
    apply Exec.assign
    have he := GraphMinor.Compute.Crossing.eval_read (a := 606)
      (GraphMinor.Compute.Crossing.eval_reg (r := 612) (by simp [s₂]) (hv.trans hn)) hiPos (by rw [hget]; exact hposition)
    simpa only [hget] using he
  have hk₃ : Keeps [611, 612, 613] [] s s₃ :=
    (((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
  have h604₃ := h604.of_preserve (hk₃.2 604 (by simp)) (hk₃.1 614 (by decide))
  have h605₃ := h605.of_preserve (hk₃.2 605 (by simp)) (hk₃.1 615 (by decide))
  have h606₃ : s₃.arrs 606 = gm06StackPositions n (input.length + 1) vertices := (hk₃.2 606 (by simp)).trans h606
  have hcond := eval_exprEq hw (GraphMinor.Compute.Crossing.eval_reg (w := w) (r := 613) (s := s₃) (by simp [s₃]) hposition)
    (GraphMinor.Compute.Crossing.eval_reg ((hk₃.1 616 (by decide)).trans h616) (by omega))
  by_cases hmem : v ∈ vertices
  · have hj : vertices.idxOf v ≤ stack.length := by
      have hidx := List.idxOf_lt_length_of_mem hmem
      omega
    have hne : position ≠ input.length + 1 := by
      dsimp only [position]
      simp only [hmem, ↓reduceIte]
      omega
    obtain ⟨sf, tf, hef, htf, hkf, hVf, hDf, hPf⟩ := gm06ErasePopLoop_exec head stack (vertices.idxOf v) s₃
      hw hn (by omega) (by omega) hj hnd hvertices hstackWords h604₃ h605₃ h606₃
      (by simp [s₃, position, hmem]) ((hk₃.1 616 (by decide)).trans h616)
    have hnext : next = stack.take (vertices.idxOf v) := by
      change (if v ∈ vertices then _ else _) = _
      simp only [hmem, ↓reduceIte]
      rfl
    have hnextLen : next.length = vertices.idxOf v := by rw [hnext, List.length_take_of_le hj]
    refine ⟨sf, 3 + (3 + (3 + (3 + tf))), .seq he₁ (.seq he₂ (.seq he₃
      (.ite_false (by simpa only [hne, ↓reduceIte] using hcond) hef))), ?_,
      (hk₃.mono (by simp) (by simp)).trans hkf (by simp) (by simp), ?_, ?_, ?_⟩
    · rw [hnextLen]
      omega
    · simpa only [hnext] using hVf
    · simpa only [hnext] using hDf
    · simpa only [hnext] using hPf
  · have heq : position = input.length + 1 := by simp only [position, hmem, ↓reduceIte]
    obtain ⟨sf, tf, hef, htf, hkf, hVf, hDf, hPf⟩ := gm06ErasePushProg_exec vertices stack s₃ hw hn
      (by omega) (hd.trans hheadsFit) hv hmem hvLen hroom h604₃ h605₃ h606₃
      (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂])
    have hnext : next = stack ++ [d] := by
      change (if v ∈ vertices then _ else _) = _
      simp only [hmem, ↓reduceIte]
    refine ⟨sf, 3 + (3 + (3 + (3 + tf))), .seq he₁ (.seq he₂ (.seq he₃
      (.ite_true (by simpa only [heq, ↓reduceIte] using hcond) (by decide) hef))), ?_,
      (hk₃.mono (by simp) (by simp)).trans hkf (by simp) (by simp), ?_, ?_, ?_⟩
    · rw [hnext, List.length_append, List.length_singleton]
      omega
    · simpa only [hnext, gm06WalkVertices_append_one, vertices, v] using hVf
    · simpa only [hnext] using hDf
    · simpa only [hnext, gm06WalkVertices_append_one, vertices, v] using hPf

end GraphMinor.Compute
