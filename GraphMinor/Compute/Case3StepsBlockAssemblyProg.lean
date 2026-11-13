module

public import GraphMinor.Compute.Case3StepsJoinRecordProg
public import GraphMinor.Compute.Case3Block

/-!
# Assembling the case (iii) block

Starting with the completed member section, the program inserts the four
corners, the counted edge and vertex lists, and the wall section. The order
is exactly that of `encCase3Block`. A fixed number of joins keeps the work
linear in the length of the completed block.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Assemble the sections in arrays 59, 60, 50, and 58 around member buffer 51.
Register 111 holds the compass edge count. -/
def case3BlockAssemblyProg : Cmd :=
  .seq (.assign 101 (.len 60))
    (.seq (case3JoinRecordProg 58)
      (.seq (case3RecordPrependProg 50 111)
        (.seq (case3RecordPrependProg 60 101) (case3JoinRecordProg 59))))

/-- The assembled buffer is the frozen case (iii) encoding. -/
theorem case3BlockAssemblyProg_exec {w h n : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (Kv : List ℕ) (Ke : List (ℕ × ℕ × ℕ))
    (corners : List ℕ) (members : List Case3MemberRecord)
    (hw : 1 < 2 ^ w) (hlen : (encCase3Block W Kv Ke corners members).length < 2 ^ w)
    (hwords : ∀ x ∈ encCase3Block W Kv Ke corners members, x < 2 ^ w)
    {s : State} (hwall : s.arrs 59 = W.encList) (hv : s.arrs 60 = Kv)
    (he : s.arrs 50 = encEdgeTriples Ke) (hc : s.arrs 58 = corners)
    (hm : s.arrs 51 = members.length :: members.flatMap Case3MemberRecord.enc)
    (hredges : s.regs 111 = Ke.length) :
    ∃ s' t, Exec w case3BlockAssemblyProg s s' t ∧
      t ≤ 1000 * ((encCase3Block W Kv Ke corners members).length + 1) ∧
      s'.arrs 51 = encCase3Block W Kv Ke corners members ∧
      (∀ a, a ≠ 51 → a ≠ 52 → a ≠ 53 → s'.arrs a = s.arrs a) ∧
      (∀ r < 101, s'.regs r = s.regs r) := by
  let b₀ := members.length :: members.flatMap Case3MemberRecord.enc
  let b₁ := corners ++ b₀
  let b₂ := Ke.length :: (encEdgeTriples Ke ++ b₁)
  let b₃ := Kv.length :: (Kv ++ b₂)
  have hblock : encCase3Block W Kv Ke corners members = W.encList ++ b₃ := by
    simp only [encCase3Block, b₃, b₂, b₁, b₀, List.cons_append, List.append_assoc]
  have hb₃ : ∀ x ∈ b₃, x < 2 ^ w := fun x hx => hwords x (by rw [hblock]; exact List.mem_append_right _ hx)
  have hvw : ∀ x ∈ Kv, x < 2 ^ w := fun x hx => hb₃ x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
  have hb₂ : ∀ x ∈ b₂, x < 2 ^ w := fun x hx => hb₃ x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
  have hew : ∀ x ∈ encEdgeTriples Ke, x < 2 ^ w := fun x hx => hb₂ x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
  have hb₁ : ∀ x ∈ b₁, x < 2 ^ w := fun x hx => hb₂ x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
  have hcw : ∀ x ∈ corners, x < 2 ^ w := fun x hx => hb₁ x (List.mem_append_left _ hx)
  have hb₀ : ∀ x ∈ b₀, x < 2 ^ w := fun x hx => hb₁ x (List.mem_append_right _ hx)
  have hww : ∀ x ∈ W.encList, x < 2 ^ w := fun x hx => hwords x (by rw [hblock]; exact List.mem_append_left _ hx)
  have hvlw : Kv.length < 2 ^ w := hb₃ _ List.mem_cons_self
  have helw : Ke.length < 2 ^ w := hb₂ _ List.mem_cons_self
  have hbl : (encCase3Block W Kv Ke corners members).length = W.encList.length + b₃.length := by rw [hblock, List.length_append]
  have hb₃l : b₃.length = 1 + (Kv.length + b₂.length) := by simp only [b₃, List.length_cons, List.length_append]; omega
  have hb₂l : b₂.length = 1 + ((encEdgeTriples Ke).length + b₁.length) := by simp only [b₂, List.length_cons, List.length_append]; omega
  have hb₁l : b₁.length = corners.length + b₀.length := List.length_append
  let s₀ := s.setReg 101 Kv.length
  have hex₀ : Exec w (.assign 101 (.len 60)) s s₀ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hv, hvlw, ↓reduceIte])
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, harr₁, hreg₁⟩ :=
    case3JoinRecordProg_exec 58 (by decide) corners b₀ hw (by omega) hcw hb₀ hc hm
      (s := s₀)
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, harr₂, hreg₂⟩ :=
    case3RecordPrependProg_exec 50 111 (by decide) (by decide) (encEdgeTriples Ke) b₁ Ke.length hw
      (by simp only [List.length_append]; omega) hew hb₁ helw
      ((harr₁ 50 (by decide) (by decide) (by decide)).trans he) hbuf₁
      (by rw [hreg₁ 111 (by dsimp only [Reg]; omega), State.setReg_regs_ne _ _ (by decide)]; exact hredges)
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuf₃, harr₃, hreg₃⟩ :=
    case3RecordPrependProg_exec 60 101 (by decide) (by decide) Kv b₂ Kv.length hw
      (by simp only [List.length_append]; omega) hvw hb₂ hvlw
      ((harr₂ 60 (by decide) (by decide) (by decide)).trans
        ((harr₁ 60 (by decide) (by decide) (by decide)).trans hv)) hbuf₂
      (by rw [hreg₂ 101 (by dsimp only [Reg]; omega), hreg₁ 101 (by dsimp only [Reg]; omega), State.setReg_regs_self])
  obtain ⟨s₄, t₄, hex₄, ht₄, hbuf₄, harr₄, hreg₄⟩ :=
    case3JoinRecordProg_exec 59 (by decide) W.encList b₃ hw (by omega) hww hb₃
      ((harr₃ 59 (by decide) (by decide) (by decide)).trans
        ((harr₂ 59 (by decide) (by decide) (by decide)).trans
          ((harr₁ 59 (by decide) (by decide) (by decide)).trans hwall))) hbuf₃
  have hex : Exec w case3BlockAssemblyProg s s₄ (2 + (t₁ + (t₂ + (t₃ + t₄)))) :=
    .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))
  refine ⟨s₄, _, hex, ?_, hbuf₄.trans hblock.symm, ?_, ?_⟩
  · omega
  · intro a h51 h52 h53
    exact (harr₄ a h51 h52 h53).trans ((harr₃ a h51 h52 h53).trans
      ((harr₂ a h51 h52 h53).trans (harr₁ a h51 h52 h53)))
  · intro r hr
    have hr' : r < 124 := by romega
    rw [hreg₄ r hr', hreg₃ r hr', hreg₂ r hr', hreg₁ r hr',
      State.setReg_regs_ne _ _ (by romega)]

end GraphMinor.Compute
