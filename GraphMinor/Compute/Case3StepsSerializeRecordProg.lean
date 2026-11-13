module

public import GraphMinor.Compute.Case3StepsRecordPrefixProg
public import GraphMinor.Compute.Case3StepsBranchRecordBounds

/-!
# Serializing one computed member record

The leaf list is copied first. The parent section and its tree-size header,
the expanded edge section and its edge-count header, and finally the vertex
section and its vertex-count header are placed before it. There are only
three joins, so copying the accumulating suffix still takes linear time.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Serialize the four computed member lists into record buffer 51. -/
def case3SerializeRecordProg : Cmd :=
  .seq (.assign 101 (.len 47))
    (.seq (copyArrLoopProg 49 51 125 126)
      (.seq (case3RecordPrependProg 48 102)
        (.seq (case3RecordPrependProg 50 111) (case3RecordPrependProg 47 101))))

/-- A record with the parser's list lengths and tree-size bound is written
exactly, in linear vertex and edge work. Only the three buffers and high
scratch registers change. -/
theorem case3SerializeRecordProg_exec {w : ℕ} (r : Case3MemberRecord)
    (hpar : r.parList.length = r.t_len) (htau : r.tauList.length = r.eList.length)
    (htree : r.t_len ≤ 2 * r.eList.length + 1)
    (hw : 1 < 2 ^ w) (hlen : r.enc.length < 2 ^ w)
    (hwords : ∀ x ∈ r.enc, x < 2 ^ w) {s : State}
    (hv : s.arrs 47 = r.vList) (he : s.arrs 50 = encEdgeTriples r.eList)
    (hp : s.arrs 48 = r.parList) (ht : s.arrs 49 = r.tauList)
    (hrtree : s.regs 102 = r.t_len) (hredges : s.regs 111 = r.eList.length) :
    ∃ s' t, Exec w case3SerializeRecordProg s s' t ∧
      t ≤ 1000 * (r.vList.length + r.eList.length + 1) ∧ s'.arrs 51 = r.enc ∧
      (∀ a, a ≠ 51 → a ≠ 52 → a ≠ 53 → s'.arrs a = s.arrs a) ∧
      (∀ r < 101, s'.regs r = s.regs r) := by
  have hlenr : r.enc.length = r.vList.length + 4 * r.eList.length + r.t_len + 3 := by
    simp only [Case3MemberRecord.enc, List.length_cons, List.length_append,
      case3Length_encEdgeTriples, hpar, htau]
    omega
  have hvw : r.vList.length < 2 ^ w := by omega
  have htw : r.tauList.length < 2 ^ w := by omega
  have hvwords : ∀ x ∈ r.vList, x < 2 ^ w := by
    intro x hx
    exact hwords x (by simp only [Case3MemberRecord.enc, List.mem_append, List.mem_cons, hx, or_true, true_or])
  have hewords : ∀ x ∈ encEdgeTriples r.eList, x < 2 ^ w := by
    intro x hx
    exact hwords x (by simp only [Case3MemberRecord.enc, List.mem_append, List.mem_cons, hx, or_true, true_or])
  have hpwords : ∀ x ∈ r.parList, x < 2 ^ w := by
    intro x hx
    exact hwords x (by simp only [Case3MemberRecord.enc, List.mem_append, List.mem_cons, hx, or_true, true_or])
  have htwords : ∀ x ∈ r.tauList, x < 2 ^ w := by
    intro x hx
    exact hwords x (by simp only [Case3MemberRecord.enc, List.mem_append, List.mem_cons, hx, or_true])
  have htreew : r.t_len < 2 ^ w := hwords _ (by simp [Case3MemberRecord.enc])
  have hedgewords : r.eList.length < 2 ^ w := hwords _ (by simp [Case3MemberRecord.enc])
  let b₁ := r.t_len :: (r.parList ++ r.tauList)
  let b₂ := r.eList.length :: (encEdgeTriples r.eList ++ b₁)
  have hb₁words : ∀ x ∈ b₁, x < 2 ^ w := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact htreew
    · rcases List.mem_append.mp hx with hx | hx
      · exact hpwords x hx
      · exact htwords x hx
  have hb₂words : ∀ x ∈ b₂, x < 2 ^ w := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hedgewords
    · rcases List.mem_append.mp hx with hx | hx
      · exact hewords x hx
      · exact hb₁words x hx
  have hb₁len : b₁.length = 1 + r.t_len + r.eList.length := by
    simp only [b₁, List.length_cons, List.length_append, hpar, htau]
    omega
  have hb₂len : b₂.length = 2 + 4 * r.eList.length + r.t_len := by
    simp only [b₂, List.length_cons, List.length_append, case3Length_encEdgeTriples, hb₁len]
    omega
  let s₀ := s.setReg 101 r.vList.length
  have hex₀ : Exec w (.assign 101 (.len 47)) s s₀ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hv, hvw, ↓reduceIte])
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, harr₁, hreg₁⟩ := copyArrLoopProg_exec 49 51 125 126
    (by decide) (by decide) hw s₀ (by change (s.arrs 49).length < 2 ^ w; rw [ht]; exact htw)
    (by change ∀ x ∈ s.arrs 49, x < 2 ^ w; rw [ht]; exact htwords)
  have hsuf₁ : s₁.arrs 51 = r.tauList := hbuf₁.trans ht
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, harr₂, hreg₂⟩ :=
    case3RecordPrependProg_exec 48 102 (by decide) (by decide) r.parList r.tauList r.t_len hw
      (by simp only [List.length_append, hpar, htau]; omega) hpwords htwords htreew
      ((harr₁ 48 (by decide)).trans hp) hsuf₁
      (by rw [hreg₁ 102 (by decide) (by decide), State.setReg_regs_ne _ _ (by decide)]; exact hrtree)
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuf₃, harr₃, hreg₃⟩ :=
    case3RecordPrependProg_exec 50 111 (by decide) (by decide) (encEdgeTriples r.eList) b₁ r.eList.length hw
      (by simp only [List.length_append, case3Length_encEdgeTriples, hb₁len]; omega)
      hewords hb₁words hedgewords
      ((harr₂ 50 (by decide) (by decide) (by decide)).trans ((harr₁ 50 (by decide)).trans he)) hbuf₂
      (by rw [hreg₂ 111 (by decide), hreg₁ 111 (by decide) (by decide), State.setReg_regs_ne _ _ (by decide)]; exact hredges)
  obtain ⟨s₄, t₄, hex₄, ht₄, hbuf₄, harr₄, hreg₄⟩ :=
    case3RecordPrependProg_exec 47 101 (by decide) (by decide) r.vList b₂ r.vList.length hw
      (by simp only [List.length_append, hb₂len]; omega) hvwords hb₂words hvw
      ((harr₃ 47 (by decide) (by decide) (by decide)).trans
        ((harr₂ 47 (by decide) (by decide) (by decide)).trans ((harr₁ 47 (by decide)).trans hv))) hbuf₃
      (by rw [hreg₃ 101 (by decide), hreg₂ 101 (by decide), hreg₁ 101 (by decide) (by decide), State.setReg_regs_self])
  have hex : Exec w case3SerializeRecordProg s s₄ (2 + (t₁ + (t₂ + (t₃ + t₄)))) :=
    .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))
  refine ⟨s₄, 2 + (t₁ + (t₂ + (t₃ + t₄))), hex, ?_, ?_, ?_, ?_⟩
  · change t₁ ≤ 8 + 15 * (s.arrs 49).length at ht₁
    rw [ht] at ht₁
    simp only [hpar, htau, case3Length_encEdgeTriples, hb₁len, hb₂len] at ht₁ ht₂ ht₃ ht₄
    omega
  · simpa only [b₂, b₁, Case3MemberRecord.enc, List.cons_append, List.append_assoc] using hbuf₄
  · intro a h51 h52 h53
    exact (harr₄ a h51 h52 h53).trans ((harr₃ a h51 h52 h53).trans
      ((harr₂ a h51 h52 h53).trans (harr₁ a h51)))
  · intro r hr
    rw [hreg₄ r (by romega), hreg₃ r (by romega), hreg₂ r (by romega),
      hreg₁ r (by romega) (by romega), State.setReg_regs_ne _ _ (by romega)]

end GraphMinor.Compute
