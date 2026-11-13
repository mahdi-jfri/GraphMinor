module

public import GraphMinor.Compute.GM02FindSavedFrame
public import GraphMinor.Compute.GM02RestoreFrameHeader
public import GraphMinor.Compute.GM02RestoreFrameArrays
public import GraphMinor.Compute.GM02ClearSavedSlice

/-!
# Restoring and popping a complete parent frame

Locate the last frame by its footer, restore its header and three
arrays, clear the saved words, and move the stack cursor back to the
frame start. The five loop-state values are recovered in the control
block. Registers below that block, including the child's answer, are
preserved throughout the return operation.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Restore the parent frame using a consecutive control block based at `b`. -/
def gm02RestoreFrameProg (stack scratch parent left right : Arr) (b : Reg) : Cmd :=
  .seq (gm02FindSavedFrameProg stack (b + 10) (b + 8) (b + 11) (b + 9))
    (.seq (gm02RestoreFrameHeaderProg stack (b + 8) (b + 9) b)
      (.seq (gm02RestoreFrameArraysProg stack parent left right (b + 9) b (b + 1) (b + 2) (b + 13))
        (.seq (gm02ClearSavedSliceProg stack scratch (b + 8) (b + 11) (b + 13))
          (.assign (b + 10) (.reg (b + 8))))))

/-- Popping restores the exact parent data and loop state while preserving the child's answer. -/
theorem gm02RestoreFrameProg_exec {w cap : ℕ} (stack scratch parent left right : Arr) (b : Reg)
    (hsp : stack ≠ parent) (hsl : stack ≠ left) (hsr : stack ≠ right) (hss : scratch ≠ stack)
    (hpl : parent ≠ left) (hpr : parent ≠ right) (hlr : left ≠ right)
    (hps : parent ≠ scratch) (hls : left ≠ scratch) (hrs : right ≠ scratch)
    (P L R pref : List ℕ) (mode code aggregate leftAnswer catalogue : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : pref.length + 9 + P.length + L.length + R.length < 2 ^ w)
    (hpw : ∀ v ∈ P, v < 2 ^ w) (hlw : ∀ v ∈ L, v < 2 ^ w) (hrw : ∀ v ∈ R, v < 2 ^ w)
    (hheader : ∀ v ∈ gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue, v < 2 ^ w)
    (hstack : s.arrs stack = pref ++
      gm02SavedFrameWords P L R mode code aggregate leftAnswer catalogue pref.length ++
        List.replicate cap 0)
    (hpos : s.regs (b + 10) = pref.length + 9 + P.length + L.length + R.length) :
    ∃ s' t, Exec w (gm02RestoreFrameProg stack scratch parent left right b) s s' t ∧
      t ≤ 34 * (P.length + L.length + R.length) + 293 ∧
      s'.arrs parent = P ∧ s'.arrs left = L ∧ s'.arrs right = R ∧
      s'.regs (b + 3) = mode ∧ s'.regs (b + 4) = code ∧
      s'.regs (b + 5) = aggregate ∧ s'.regs (b + 6) = leftAnswer ∧
      s'.regs (b + 7) = catalogue ∧ s'.regs (b + 10) = pref.length ∧
      IsPrefixBuffer stack pref (9 + P.length + L.length + R.length + cap) s' ∧
      (∀ r < b, s'.regs r = s.regs r) := by
  let H := gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue
  let F := gm02SavedFrameWords P L R mode code aggregate leftAnswer catalogue pref.length
  obtain ⟨s₁, he₁, hstart₁, hlen₁, _, ha₁, hr₁⟩ := gm02FindSavedFrameProg_exec stack
    (b + 10) (b + 8) (b + 11) (b + 9)
    (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)
    (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)
    P L R pref mode code aggregate leftAnswer catalogue s hlen hstack hpos
  have hstack₁ : s₁.arrs stack = pref ++ H ++ P ++ L ++ R ++ [pref.length] ++ List.replicate cap 0 := by
    simpa only [H, gm02SavedFrameWords, List.append_assoc] using (congrFun ha₁ stack).trans hstack
  obtain ⟨s₂, t₂, he₂, ht₂, hP₂, hL₂, hR₂, hm₂, hc₂, ha₂, hl₂, ht₂', hread₂, hstart₂, harr₂, hreg₂⟩ :=
    gm02RestoreFrameHeaderProg_exec stack (b + 8) (b + 9) b
      (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)
      P L R (P ++ L ++ R ++ [pref.length] ++ List.replicate cap 0)
      mode code aggregate leftAnswer catalogue s₁ hw (by omega) hheader
      ⟨pref, rfl, by simpa only [List.append_assoc] using hstack₁⟩ hstart₁
  have hstack₂ : s₂.arrs stack = (pref ++ H) ++ P ++ L ++ R ++ ([pref.length] ++ List.replicate cap 0) := by
    simpa only [List.append_assoc] using (congrFun harr₂ stack).trans hstack₁
  obtain ⟨s₃, t₃, he₃, ht₃, hP₃, hL₃, hR₃, _, harr₃, hreg₃⟩ :=
    gm02RestoreFrameArraysProg_exec stack parent left right (b + 9) b (b + 1) (b + 2) (b + 13)
      hsp hsl hsr hpl hpr hlr (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)
      (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)
      (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)
      (pref ++ H) P L R ([pref.length] ++ List.replicate cap 0) s₂ hw hpw hlw hrw
      (by simp only [List.length_append, H, gm02SavedFrameHeader_length]; omega) hstack₂
      (by simpa only [List.length_append, H, gm02SavedFrameHeader_length] using hread₂) hP₂ hL₂ hR₂
  have hstart₃ := (hreg₃ (b + 8) (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)).trans hstart₂
  have hframeLen₂ := (hreg₂ (b + 11) (by dsimp only [Reg]; omega)
    (Or.inr (by dsimp only [Reg]; omega))).trans hlen₁
  have hframeLen₃ := (hreg₃ (b + 11) (by dsimp only [Reg]; omega)
    (by dsimp only [Reg]; omega)).trans hframeLen₂
  have hstack₃ : s₃.arrs stack = pref ++ F ++ List.replicate cap 0 := by
    rw [harr₃ stack hsp hsl hsr, congrFun harr₂ stack, congrFun ha₁ stack]
    exact hstack
  obtain ⟨s₄, t₄, he₄, ht₄, hbuffer₄, harr₄, hreg₄⟩ :=
    gm02ClearSavedSliceProg_exec stack scratch (b + 8) (b + 11) (b + 13) hss
      (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega) pref F s₃ hw
      (by simpa only [F, gm02SavedFrameWords_length, Nat.add_assoc] using hlen)
      hstack₃ hstart₃ (by simpa only [F, gm02SavedFrameWords_length] using hframeLen₃)
  have hstart₄ := (hreg₄ (b + 8) (by dsimp only [Reg]; omega)).trans hstart₃
  let s₅ := s₄.setReg (b + 10) pref.length
  have he₅ : Exec w (.assign (b + 10) (.reg (b + 8))) s₄ s₅ 2 :=
    Exec.assign (by simp [Expr.eval, hstart₄, checkWord_of_lt (by omega : pref.length < 2 ^ w)])
  have keep (r : Reg) (hr : r < b + 8) : s₅.regs r = s₂.regs r := by
    rw [State.setReg_regs_ne _ _ (by dsimp only [Reg] at *; omega)]
    exact (hreg₄ r (by dsimp only [Reg] at *; omega)).trans
      (hreg₃ r (by dsimp only [Reg] at *; omega) (by dsimp only [Reg] at *; omega))
  refine ⟨s₅, 13 + (t₂ + (t₃ + (t₄ + 2))), Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅))),
    ?_, (harr₄ parent hsp.symm hps).trans hP₃, (harr₄ left hsl.symm hls).trans hL₃,
    (harr₄ right hsr.symm hrs).trans hR₃,
    (keep _ (by dsimp only [Reg]; omega)).trans hm₂, (keep _ (by dsimp only [Reg]; omega)).trans hc₂,
    (keep _ (by dsimp only [Reg]; omega)).trans ha₂, (keep _ (by dsimp only [Reg]; omega)).trans hl₂,
    (keep _ (by dsimp only [Reg]; omega)).trans ht₂', by simp [s₅], ?_, ?_⟩
  · simp only [F, gm02SavedFrameWords_length] at ht₄
    omega
  · simpa only [IsPrefixBuffer, s₅, State.setReg_arrs, F, gm02SavedFrameWords_length] using hbuffer₄
  · intro r hrb
    exact (keep r (by dsimp only [Reg] at *; omega)).trans
      ((hreg₂ r (by dsimp only [Reg] at *; omega) (Or.inl hrb)).trans
        (hr₁ r (by dsimp only [Reg] at *; omega) (by dsimp only [Reg] at *; omega)
          (by dsimp only [Reg] at *; omega)))

end GraphMinor.Compute
