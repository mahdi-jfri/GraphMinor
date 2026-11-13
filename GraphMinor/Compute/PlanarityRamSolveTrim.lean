module

public import GraphMinor.Compute.PlanarityRamSolveMerge
import GraphMinor.Compute.WhileRounds

/-!
# `TRIM` on the Word RAM

Part I, Section 5 of the planarity note removes the returns to the parent
depth `c` from the summary of a finished vertex:

    if S.least = c: S := empty
    else: pop whole blocks with minimum c, then drop the depth-c returns
          from the front of both lists of the new top block

This file gives the RAM program `trimProg` and proves that it refines the Lean
function `trim` (`trimProg_spec`). The summary pointer is in register 57 and
`c` in register 62.

The time of a trim is linear in the number of removed blocks and returns. To
pay for it, `weight` gives each summary 120 steps per block and 10 per return.
A trim costs at most 100 steps plus the weight it removes. A merge keeps all
returns, so `mergeProg_spec` gives the same kind of bound.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-! ### Weights -/

/-- The number of returns in a block stack. -/
def stackNodes : List Block → ℕ
  | [] => 0
  | b :: bs => b.left.length + b.right.length + stackNodes bs

/-- The number of returns of a summary. -/
def nodeCount (S : Summary) : ℕ := S.anchor.length + stackNodes S.blocks

/-- The potential of a summary: 120 steps per block and 10 per return. -/
def weight : Option Summary → ℕ
  | none => 0
  | some S => 120 * S.blocks.length + 10 * nodeCount S

theorem BlockChain.nodes_length {s : State} {cap p : ℕ} {bs ns : List ℕ} {stack : List Block}
    (h : BlockChain s cap p bs ns stack) : ns.length = stackNodes stack := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ hleft hright _ ih =>
    simp only [List.length_append, stackNodes, ih, hleft.1.length_eq, hright.1.length_eq]

theorem SummaryAt.nodes_length {s : State} {M p : ℕ} {S : Summary} {bs ns : List ℕ}
    (h : SummaryAt s M p S bs ns) : ns.length = nodeCount S := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hA, hB, rfl, _, _⟩ := h
  simp only [List.length_append, nodeCount, hA.1.length_eq, hB.nodes_length]

theorem SummaryAt.blocks_length {s : State} {M p : ℕ} {S : Summary} {bs ns : List ℕ}
    (h : SummaryAt s M p S bs ns) : bs.length = S.blocks.length := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hB, _, _, _⟩ := h
  exact hB.length_eq

/-! ### The minimum of the top block -/

/-- A list minimum read from memory is at most `D`. -/
theorem ListAt.listMinimum_le {s : State} {cap f l D : ℕ} {A : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x) (hW : Words D s) : listMinimum x ≤ D := by
  by_cases hx : x = []
  · subst hx; exact Nat.zero_le _
  · have := hW.get (by simp [Field.array]) (by simp [Field.array]) (h.last_depth hx)
    simpa [listMinimum, List.getLast?_eq_some_getLast hx] using this

/-- `73 := Block.minimum` of the block whose headers are in registers 68–71. -/
def minProg : Cmd :=
  .ite (.reg 68)
    (.ite (.reg 70)
      (.seq (lastDepthProg 72 69) (.seq (lastDepthProg 73 71)
        (.ite (.op .lt (.reg 72) (.reg 73)) (.assign 73 (.reg 72)) .skip)))
      (lastDepthProg 73 69))
    (lastDepthProg 73 71)

private theorem list_eq_nil {s : State} {cap f l : ℕ} {A : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x) (hf : f = 0) : x = [] := by
  have hA := h.first_eq_zero_iff.mp hf
  have := h.1.length_eq
  rw [hA] at this
  exact List.length_eq_zero_iff.mp this.symm

private theorem list_ne_nil {s : State} {cap f l : ℕ} {A : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x) (hf : f ≠ 0) : x ≠ [] := fun hx => hf (by
  have := h.1.length_eq
  rw [hx] at this
  exact h.first_eq_zero_iff.mpr (List.length_eq_zero_iff.mp this))

theorem minProg_spec {w D cap : ℕ} {s : State} {LA RA : List ℕ} {x y : List ReturnNode}
    (hL : ListAt s cap (s.regs 68) (s.regs 69) LA x)
    (hR : ListAt s cap (s.regs 70) (s.regs 71) RA y)
    (hW : Words D s) (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) :
    ∃ s' t, Exec w minProg s s' t ∧ t ≤ 16 ∧ s'.arrs = s.arrs ∧
      s'.regs 73 = Block.minimum ⟨x, y⟩ ∧ (∀ r : ℕ, r ≠ 72 → r ≠ 73 → s'.regs r = s.regs r) := by
  have hpL := hL.pointers_lt hcap
  have hpR := hR.pointers_lt hcap
  have hmx := hL.listMinimum_le hW
  have hmy := hR.listMinimum_le hW
  by_cases h68 : s.regs 68 = 0
  · have hx := list_eq_nil hL h68
    subst hx
    obtain ⟨t, hx, ht⟩ := lastDepthProg_spec (dst := 73) hR hcap hcapD hD hW
    refine ⟨_, _, exec_ite_zero h68 hx, by omega, rfl, by simp [Block.minimum], fun r h1 h2 => ?_⟩
    simp [h2]
  · have hx := list_ne_nil hL h68
    have hxe : x.isEmpty = false := by simpa using hx
    by_cases h70 : s.regs 70 = 0
    · have hy := list_eq_nil hR h70
      subst hy
      obtain ⟨t, hx', ht⟩ := lastDepthProg_spec (dst := 73) hL hcap hcapD hD hW
      refine ⟨_, _, exec_ite_pos h68 (by omega) (exec_ite_zero h70 hx'), by omega, rfl,
        by simp [Block.minimum, hxe], fun r h1 h2 => ?_⟩
      simp [h2]
    · have hy := list_ne_nil hR h70
      have hye : y.isEmpty = false := by simpa using hy
      obtain ⟨t₁, hx₁, ht₁⟩ := lastDepthProg_spec (dst := 72) hL hcap hcapD hD hW
      let s₁ := s.setReg 72 (listMinimum x)
      have hR₁ : ListAt s₁ cap (s₁.regs 70) (s₁.regs 71) RA y := by
        simpa [s₁] using hR.of_arrs_eq (s' := s₁) rfl
      obtain ⟨t₂, hx₂, ht₂⟩ := lastDepthProg_spec (dst := 73) hR₁ hcap hcapD hD hW
      let s₂ := s₁.setReg 73 (listMinimum y)
      have hlt : (Expr.op .lt (.reg 72) (.reg 73)).eval w s₂ =
          some (if listMinimum x < listMinimum y then 1 else 0) := by
        rw [eval_op (eval_reg (by simp [s₂, s₁]; omega)) (eval_reg (by simp [s₂]; omega)),
          binop_lt (by omega)]
        simp [s₂, s₁]
      have hmin : Block.minimum ⟨x, y⟩ = min (listMinimum x) (listMinimum y) := by
        simp [Block.minimum, hxe, hye]
      by_cases hc : listMinimum x < listMinimum y
      · have hx₃ : Exec w (.assign 73 (.reg 72)) s₂ (s₂.setReg 73 (listMinimum x)) 2 := by
          have := exec_mov (w := w) (s := s₂) (dst := 73) (src := 72) (by simp [s₂, s₁]; omega)
          simpa [s₂, s₁] using this
        have hx := exec_ite_pos (c₂ := lastDepthProg 73 71) h68 (by omega)
          (exec_ite_pos (c₂ := lastDepthProg 73 69) h70
          (by omega) (Exec.seq hx₁ (Exec.seq hx₂
            (exec_ite_eval (c₂ := .skip) hlt (fun _ => hx₃) (fun h => by simp [hc] at h)))))
        refine ⟨_, _, hx, by simp; omega, rfl, by simp [hmin]; omega, fun r h1 h2 => ?_⟩
        simp [s₂, s₁, h1, h2]
      · have hx := exec_ite_pos (c₂ := lastDepthProg 73 71) h68 (by omega)
          (exec_ite_pos (c₂ := lastDepthProg 73 69) h70
          (by omega) (Exec.seq hx₁ (Exec.seq hx₂
            (exec_ite_eval (c₁ := .assign 73 (.reg 72)) hlt (fun h => by simp [hc] at h)
              (fun _ => Exec.skip s₂)))))
        refine ⟨_, _, hx, by simp; omega, rfl, by simp [s₂, hmin]; omega, fun r h1 h2 => ?_⟩
        simp [s₂, s₁, h1, h2]

/-! ### The pop test -/

/-- One if the top block has minimum `c`, and zero otherwise or for the
empty stack. -/
def trimTestVal (c : ℕ) : List Block → ℕ
  | [] => 0
  | q :: _ => if q.minimum = c then 1 else 0

/-- `74 := trimTestVal c` for the stack at register 67, with `c` in register 62. -/
def trimTestProg' : Cmd :=
  .ite (.reg 67)
    (.seq loadBlockProg (.seq minProg (.assign 74 (.op .eq (.reg 73) (.reg 62)))))
    (.assign 74 (.const 0))

theorem trimTestProg'_spec {w D cap : ℕ} {s : State} {bs ns : List ℕ} {stack : List Block}
    (hB : BlockChain s cap (s.regs 67) bs ns stack) (hW : Words D s) (hc : s.regs 62 ≤ D)
    (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) :
    ∃ s' t, Exec w trimTestProg' s s' t ∧ t ≤ 35 ∧ s'.arrs = s.arrs ∧
      s'.regs 74 = trimTestVal (s.regs 62) stack ∧
      (∀ r : ℕ, r < 68 ∨ 74 < r → s'.regs r = s.regs r) := by
  have h67 := hB.top_lt hcap
  obtain ⟨q, hq⟩ : ∃ q, s.regs 67 = q := ⟨_, rfl⟩
  rw [hq] at hB
  cases hB with
  | nil =>
    have hx := exec_ite_zero (w := w)
      (c₁ := .seq loadBlockProg (.seq minProg (.assign 74 (.op .eq (.reg 73) (.reg 62))))) hq
      (exec_setc (dst := 74) (n := 0) (by omega))
    refine ⟨_, _, hx, by omega, rfl, by simp [trimTestVal], fun r hr => ?_⟩
    simp [show r ≠ 74 by omega]
  | @cons _ below lf ll rf rl bs' ns' L R blk rest hpos hqc hlf hll hrf hrl hbelow hL hR hrest =>
    rw [← hq] at hlf hll hrf hrl
    have hpL := hL.pointers_lt hcap
    have hpR := hR.pointers_lt hcap
    let s₁ := (((s.setReg 68 lf).setReg 69 ll).setReg 70 rf).setReg 71 rl
    have hx₁ : Exec w loadBlockProg s s₁ 12 :=
      loadBlockProg_exec (by omega) hlf hll hrf hrl ⟨by omega, by omega, by omega, by omega⟩
    have hL₁ : ListAt s₁ cap (s₁.regs 68) (s₁.regs 69) L blk.left := by
      simpa [s₁] using hL.of_arrs_eq (s' := s₁) rfl
    have hR₁ : ListAt s₁ cap (s₁.regs 70) (s₁.regs 71) R blk.right := by
      simpa [s₁] using hR.of_arrs_eq (s' := s₁) rfl
    obtain ⟨s₂, t₂, hx₂, ht₂, harr₂, h73₂, hregs₂⟩ := minProg_spec hL₁ hR₁ hW hcap hcapD hD
    replace h73₂ : s₂.regs 73 = blk.minimum := h73₂
    have hmD : blk.minimum ≤ D := by
      have h1 := hL.listMinimum_le hW
      have h2 := hR.listMinimum_le hW
      simp only [Block.minimum]
      split_ifs <;> omega
    have h62₂ : s₂.regs 62 = s.regs 62 := by
      rw [hregs₂ 62 (by decide) (by decide)]; simp [s₁]
    have heq : (Expr.op .eq (.reg 73) (.reg 62)).eval w s₂ =
        some (if blk.minimum = s.regs 62 then 1 else 0) := by
      rw [eval_op (eval_reg (by rw [h73₂]; omega)) (eval_reg (by rw [h62₂]; omega)),
        binop_eq (by omega), h73₂, h62₂]
    have hx₃ := Exec.assign (r := 74) heq
    have hx := exec_ite_pos (c₂ := .assign 74 (.const 0)) (by omega : s.regs 67 ≠ 0) (by omega)
      (Exec.seq hx₁ (Exec.seq hx₂ hx₃))
    refine ⟨_, _, hx, by simp; omega, by simp [harr₂]; rfl, by simp [trimTestVal], fun r hr => ?_⟩
    simp only [State.setReg_regs, show r ≠ 74 by omega, ↓reduceIte]
    rw [hregs₂ r (by omega) (by omega)]
    simp [s₁, show r ≠ 68 by omega, show r ≠ 69 by omega,
      show r ≠ 70 by omega, show r ≠ 71 by omega]

/-! ### Trimming the lists of the top block -/

theorem Words.of_arrs_eq {D : ℕ} {s s' : State} (h : Words D s) (he : s'.arrs = s.arrs) :
    Words D s' := fun a h1 h2 x hx => h a h1 h2 x (by rw [he] at hx; exact hx)

/-- Drop the depth-`c` returns from the front of both lists of the top block
at register 67, with `c` in register 62, and store the new headers. -/
def trimTopProg : Cmd :=
  .seq loadBlockProg
    (.seq (trimListProg 68 69 62 74)
      (.seq (trimListProg 70 71 62 74)
        (.seq (.write Field.blockLeftFirst.array (.reg 67) (.reg 68))
          (.seq (.write Field.blockLeftLast.array (.reg 67) (.reg 69))
            (.seq (.write Field.blockRightFirst.array (.reg 67) (.reg 70))
              (.write Field.blockRightLast.array (.reg 67) (.reg 71)))))))

/-- The top block after trimming at depth `c`. -/
abbrev trimTop (c : ℕ) (q : Block) : Block :=
  ⟨q.left.dropWhile (depthIs c), q.right.dropWhile (depthIs c)⟩

theorem trimTopProg_spec {w D cap : ℕ} {s : State} {bs ns : List ℕ} {q : Block}
    {rest : List Block}
    (hB : BlockChain s cap (s.regs 67) bs ns (q :: rest)) (hnd : bs.Nodup) (hW : Words D s)
    (hc : s.regs 62 ≤ D) (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) :
    ∃ s' t ns', Exec w trimTopProg s s' t ∧
      t + 10 * ((trimTop (s.regs 62) q).left.length + (trimTop (s.regs 62) q).right.length) ≤
        44 + 10 * (q.left.length + q.right.length) ∧
      BlockChain s' cap (s'.regs 67) bs ns' (trimTop (s.regs 62) q :: rest) ∧ ns'.Sublist ns ∧
      Frame s s' (fun a r => r = s.regs 67 ∧ IsBlockArr a) ∧ Words D s' ∧
      (∀ r : ℕ, r < 68 ∨ 74 < r → s'.regs r = s.regs r) := by
  set c := s.regs 62 with hcdef
  obtain ⟨p, hp⟩ : ∃ p, s.regs 67 = p := ⟨_, rfl⟩
  rw [hp] at hB
  cases hB with
  | @cons _ below lf ll rf rl bs' ns' L R _ _ hpos hqc hlf hll hrf hrl hbelow hL hR hrest =>
  subst hp
  have hpL := hL.pointers_lt hcap
  have hpR := hR.pointers_lt hcap
  have hpw : s.regs 67 < 2 ^ w := by omega
  let s₁ := (((s.setReg 68 lf).setReg 69 ll).setReg 70 rf).setReg 71 rl
  have hx₁ : Exec w loadBlockProg s s₁ 12 :=
    loadBlockProg_exec hpw hlf hll hrf hrl ⟨by omega, by omega, by omega, by omega⟩
  have hL₁ : ListAt s₁ cap (s₁.regs 68) (s₁.regs 69) L q.left := by
    simpa [s₁] using hL.of_arrs_eq (s' := s₁) rfl
  have hc₁ : s₁.regs 62 = c := by simp [s₁, hcdef]
  obtain ⟨s₂, t₂, A', hx₂, ht₂, harr₂, hsufA, hA₂, hregs₂⟩ :=
    trimListProg_spec (w := w) (D := D) (f := 68) (l := 69) (c := 62) (cont := 74)
      (by decide) (by decide) (by decide) (by decide) (by decide) hL₁ hcap hcapD (by omega) hW
      (by rw [hc₁]; exact hc)
  rw [hc₁] at ht₂ hA₂
  have hr₂ : ∀ r : ℕ, r ≠ 68 → r ≠ 69 → r ≠ 74 → s₂.regs r = s₁.regs r := hregs₂
  have hR₂ : ListAt s₂ cap (s₂.regs 70) (s₂.regs 71) R q.right := by
    rw [hr₂ 70 (by decide) (by decide) (by decide), hr₂ 71 (by decide) (by decide) (by decide)]
    simpa [s₁] using hR.of_arrs_eq (s' := s₂) (by rw [harr₂]; rfl)
  have hc₂ : s₂.regs 62 = c := by rw [hr₂ 62 (by decide) (by decide) (by decide), hc₁]
  obtain ⟨s₃, t₃, B', hx₃, ht₃, harr₃, hsufB, hB₃, hregs₃⟩ :=
    trimListProg_spec (w := w) (D := D) (f := 70) (l := 71) (c := 62) (cont := 74)
      (by decide) (by decide) (by decide) (by decide) (by decide) hR₂ hcap hcapD (by omega)
      (hW.of_arrs_eq (by rw [harr₂]; rfl)) (by rw [hc₂]; exact hc)
  rw [hc₂] at ht₃ hB₃
  have hr₃ : ∀ r : ℕ, r ≠ 70 → r ≠ 71 → r ≠ 74 → s₃.regs r = s₂.regs r := hregs₃
  have harr₃' : s₃.arrs = s.arrs := by rw [harr₃, harr₂]; rfl
  have hA₃ : ListAt s₃ cap (s₃.regs 68) (s₃.regs 69) A' (q.left.dropWhile (depthIs c)) := by
    rw [hr₃ 68 (by decide) (by decide) (by decide), hr₃ 69 (by decide) (by decide) (by decide)]
    exact hA₂.of_arrs_eq harr₃
  have h67₃ : s₃.regs 67 = s.regs 67 := by
    rw [hr₃ 67 (by decide) (by decide) (by decide), hr₂ 67 (by decide) (by decide) (by decide)]
    simp [s₁]
  have hpA := hA₃.pointers_lt hcap
  have hpB := hB₃.pointers_lt hcap
  have hlen : ∀ a, (s₃.arrs a).length = (s.arrs a).length := fun a => by rw [harr₃']
  have hpl : ∀ a, IsBlockArr a → s.regs 67 < (s.arrs a).length := by
    intro a ha
    simp only [IsBlockArr] at ha
    rcases ha with ha | ha | ha | ha | ha <;> subst ha
    · exact (List.getElem?_eq_some_iff.mp hlf).1
    · exact (List.getElem?_eq_some_iff.mp hll).1
    · exact (List.getElem?_eq_some_iff.mp hrf).1
    · exact (List.getElem?_eq_some_iff.mp hrl).1
    · exact (List.getElem?_eq_some_iff.mp hbelow).1
  set P := s.regs 67 with hPdef
  let s₄ := s₃.writeArr Field.blockLeftFirst.array P (s₃.regs 68)
  let s₅ := s₄.writeArr Field.blockLeftLast.array P (s₃.regs 69)
  let s₆ := s₅.writeArr Field.blockRightFirst.array P (s₃.regs 70)
  let s₇ := s₆.writeArr Field.blockRightLast.array P (s₃.regs 71)
  have hl₃ : ∀ a, IsBlockArr a → P < (s₃.arrs a).length := fun a ha => by
    rw [hlen]; exact hpl a ha
  have hl₄ : P < (s₄.arrs Field.blockLeftLast.array).length := by
    rw [(Frame.writeArr s₃ _ _ _ _).1]; exact hl₃ _ (by simp [IsBlockArr])
  have hl₅ : P < (s₅.arrs Field.blockRightFirst.array).length := by
    rw [(Frame.writeArr s₄ _ _ _ _).1, (Frame.writeArr s₃ _ _ _ _).1]
    exact hl₃ _ (by simp [IsBlockArr])
  have hl₆ : P < (s₆.arrs Field.blockRightLast.array).length := by
    rw [(Frame.writeArr s₅ _ _ _ _).1, (Frame.writeArr s₄ _ _ _ _).1,
      (Frame.writeArr s₃ _ _ _ _).1]
    exact hl₃ _ (by simp [IsBlockArr])
  have hx₇ : Exec w (.seq (.write Field.blockLeftFirst.array (.reg 67) (.reg 68))
      (.seq (.write Field.blockLeftLast.array (.reg 67) (.reg 69))
        (.seq (.write Field.blockRightFirst.array (.reg 67) (.reg 70))
          (.write Field.blockRightLast.array (.reg 67) (.reg 71))))) s₃ s₇ 12 := by
    have e1 := exec_st (w := w) (s := s₃) (a := Field.blockLeftFirst.array) (idx := 67) (val := 68)
      (by rw [h67₃]; exact hl₃ _ (by simp [IsBlockArr])) (by rw [h67₃]; exact hpw) (by omega)
    have e2 := exec_st (w := w) (s := s₄) (a := Field.blockLeftLast.array) (idx := 67) (val := 69)
      (by simp [s₄, State.writeArr_regs, h67₃]; exact hl₄) (by simp [s₄, State.writeArr_regs, h67₃]; omega)
      (by simp [s₄, State.writeArr_regs]; omega)
    have e3 := exec_st (w := w) (s := s₅) (a := Field.blockRightFirst.array) (idx := 67) (val := 70)
      (by simp [s₅, s₄, State.writeArr_regs, h67₃]; exact hl₅)
      (by simp [s₅, s₄, State.writeArr_regs, h67₃]; omega)
      (by simp [s₅, s₄, State.writeArr_regs]; omega)
    have e4 := exec_st (w := w) (s := s₆) (a := Field.blockRightLast.array) (idx := 67) (val := 71)
      (by simp [s₆, s₅, s₄, State.writeArr_regs, h67₃]; exact hl₆)
      (by simp [s₆, s₅, s₄, State.writeArr_regs, h67₃]; omega)
      (by simp [s₆, s₅, s₄, State.writeArr_regs]; omega)
    simp only [s₄, s₅, s₆, State.writeArr_regs, h67₃] at e1 e2 e3 e4
    exact Exec.seq e1 (Exec.seq e2 (Exec.seq e3 e4))
  have hF₇ : Frame s₃ s₇ (fun a r => r = P ∧ IsBlockArr a) :=
    (((Frame.writeArr s₃ _ _ _).trans (Frame.writeArr s₄ _ _ _)).trans
      (Frame.writeArr s₅ _ _ _)).trans (Frame.writeArr s₆ _ _ _) |>.mono (by
        intro a r h
        simp only [IsBlockArr]
        rcases h with ((h | h) | h) | h <;> simp [h.1, h.2])
  have hF₇b : Frame s₃ s₇ (fun a r => r = P ∧ (a = Field.blockLeftFirst.array ∨
      a = Field.blockLeftLast.array ∨ a = Field.blockRightFirst.array ∨
      a = Field.blockRightLast.array)) :=
    (((Frame.writeArr s₃ _ _ _).trans (Frame.writeArr s₄ _ _ _)).trans
      (Frame.writeArr s₅ _ _ _)).trans (Frame.writeArr s₆ _ _ _) |>.mono (by
        intro a r h
        rcases h with ((h | h) | h) | h <;> simp [h.1, h.2])
  have hnode : ∀ r, ¬ NodeCell (fun a r => r = P ∧ IsBlockArr a) r := by
    intro r; simp [NodeCell, IsBlockArr, Field.array]
  have hne : ∀ a a' : Field, a ≠ a' → a.array ≠ a'.array := fun a a' h e =>
    h (Field.array_injective e)
  have hnd' := List.nodup_cons.mp hnd
  have hx := Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ hx₇))
  have h67₇ : s₇.regs 67 = P := h67₃
  refine ⟨s₇, _, A' ++ B' ++ ns', hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := (List.dropWhile_suffix (depthIs c) (l := q.left)).length_le
    have h2 := (List.dropWhile_suffix (depthIs c) (l := q.right)).length_le
    have e1 : (trimTop c q).left = q.left.dropWhile (depthIs c) := rfl
    have e2 : (trimTop c q).right = q.right.dropWhile (depthIs c) := rfl
    rw [e1, e2]
    omega
  · rw [h67₇]
    refine BlockChain.cons (b := trimTop c q) (below := below) hpos hqc ?_ ?_ ?_ ?_ ?_
      (hA₃.frame hF₇ fun r _ => hnode r) (hB₃.frame hF₇ fun r _ => hnode r) ?_
    · simp only [s₇, s₆, s₅]
      rw [writeArr_get_ne (hne _ _ (by decide)), writeArr_get_ne (hne _ _ (by decide)),
        writeArr_get_ne (hne _ _ (by decide))]
      exact writeArr_get_self (hl₃ _ (by simp [IsBlockArr]))
    · simp only [s₇, s₆]
      rw [writeArr_get_ne (hne _ _ (by decide)), writeArr_get_ne (hne _ _ (by decide))]
      exact writeArr_get_self hl₄
    · simp only [s₇]
      rw [writeArr_get_ne (hne _ _ (by decide))]
      exact writeArr_get_self hl₅
    · exact writeArr_get_self hl₆
    · rw [hF₇b.get (by simp [Field.array]), harr₃']
      exact hbelow
    · exact (hrest.of_arrs_eq harr₃').frame hF₇
        (fun r hr => by
          simp only [BlockCell, not_or]
          have : r ≠ P := fun h => hnd'.1 (h ▸ hr)
          exact ⟨fun h => this h.1, fun h => this h.1, fun h => this h.1, fun h => this h.1,
            fun h => this h.1⟩)
        (fun r _ => hnode r)
  · exact (hsufA.sublist.append hsufB.sublist).append (List.Sublist.refl _)
  · exact (Frame.of_arrs_eq harr₃' (fun _ _ => False)).trans hF₇ |>.mono fun a r h => by
      rcases h with h | h
      · exact h.elim
      · exact h
  · have hW₃ : Words D s₃ := hW.of_arrs_eq harr₃'
    exact (((hW₃.writeArr Field.blockLeftFirst.array P (by omega : s₃.regs 68 ≤ D)).writeArr
      Field.blockLeftLast.array P (by omega : s₃.regs 69 ≤ D)).writeArr
      Field.blockRightFirst.array P (by omega : s₃.regs 70 ≤ D)).writeArr
      Field.blockRightLast.array P (by omega : s₃.regs 71 ≤ D)
  · intro r hr
    show s₃.regs r = s.regs r
    rw [hr₃ r (by omega) (by omega) (by omega), hr₂ r (by omega) (by omega) (by omega)]
    simp [s₁, show r ≠ 68 by omega, show r ≠ 69 by omega, show r ≠ 70 by omega,
      show r ≠ 71 by omega]

/-! ### Popping whole blocks -/

/-- Pop blocks while the top block has minimum `c`. -/
def popLoopProg : Cmd := .while (.reg 74) (.seq popProg trimTestProg')

theorem trimTestVal_le (c : ℕ) (stack : List Block) : trimTestVal c stack ≤ 1 := by
  cases stack with
  | nil => simp [trimTestVal]
  | cons q rest => simp only [trimTestVal]; split <;> omega

/-- The pop loop of `TRIM`: it ends at a suffix `rest` of the stack with the
same result under `trimBlocks c`, whose top block (if any) does not have
minimum `c`. Each pop costs at most 40 steps. -/
theorem popLoopProg_spec {w D cap : ℕ} {s : State} {bs ns : List ℕ} {stack : List Block}
    (hB : BlockChain s cap (s.regs 67) bs ns stack)
    (h74 : s.regs 74 = trimTestVal (s.regs 62) stack)
    (hW : Words D s) (hc : s.regs 62 ≤ D) (hcap : 0 < cap) (hcapD : cap ≤ D + 1)
    (hD : D + 1 < 2 ^ w) :
    ∃ s' t rest bs' ns', Exec w popLoopProg s s' t ∧ s'.arrs = s.arrs ∧
      BlockChain s' cap (s'.regs 67) bs' ns' rest ∧ bs' <:+ bs ∧ ns' <:+ ns ∧
      trimBlocks (s.regs 62) rest = trimBlocks (s.regs 62) stack ∧
      trimTestVal (s.regs 62) rest = 0 ∧ t + 40 * rest.length ≤ 40 * stack.length + 1 ∧
      (∀ r : ℕ, r < 67 ∨ 74 < r → s'.regs r = s.regs r) := by
  set c := s.regs 62 with hcdef
  let I : (List Block × List ℕ × List ℕ) → State → Prop := fun g s' =>
    s'.arrs = s.arrs ∧ BlockChain s' cap (s'.regs 67) g.2.1 g.2.2 g.1 ∧ g.2.1 <:+ bs ∧
      g.2.2 <:+ ns ∧ trimBlocks c g.1 = trimBlocks c stack ∧ s'.regs 74 = trimTestVal c g.1 ∧
      (∀ r : ℕ, r < 67 ∨ 74 < r → s'.regs r = s.regs r)
  have hround : ∀ g s', I g s' → ∃ v, (Expr.reg 74).eval w s' = some v ∧ (v ≠ 0 →
      ∃ g' s'' t, Exec w (.seq popProg trimTestProg') s' s'' t ∧ I g' s'' ∧
        (Expr.reg 74).cost + t + 40 * g'.1.length ≤ 40 * g.1.length) := by
    rintro ⟨rest, bs', ns'⟩ s' ⟨harr, hB', hbs, hns, htb, h74', hregs⟩
    dsimp only at harr hB' hbs hns htb h74' hregs ⊢
    have hle := trimTestVal_le c rest
    refine ⟨_, eval_reg (by omega), fun hv => ?_⟩
    have hc' : s'.regs 62 = c := hregs 62 (by omega)
    have hW' : Words D s' := hW.of_arrs_eq harr
    obtain ⟨p, hp⟩ : ∃ p, s'.regs 67 = p := ⟨_, rfl⟩
    rw [hp] at hB'
    cases hB' with
    | nil => simp [h74', trimTestVal] at hv
    | @cons _ below lf ll rf rl bs'' ns'' L R q rest' hpos hqc hlf hll hrf hrl hbelow hL hR
        hrest =>
    have hmin : q.minimum = c := by
      by_contra h
      simp [h74', trimTestVal, h] at hv
    have hbD : below ≤ D := hW'.get (by simp [Field.array]) (by simp [Field.array]) hbelow
    let s₁ := s'.setReg 67 below
    have hx₁ : Exec w popProg s' s₁ 3 :=
      exec_ld (by omega) (by rw [hp]; exact hbelow) (by omega)
    have hB₁ : BlockChain s₁ cap (s₁.regs 67) bs'' ns'' rest' := by
      simpa [s₁] using hrest.of_arrs_eq (s' := s₁) rfl
    obtain ⟨s₂, t₂, hx₂, ht₂, harr₂, h74₂, hregs₂⟩ :=
      trimTestProg'_spec (w := w) (D := D) hB₁ hW' (by simp [s₁, hc', hc]) hcap hcapD hD
    have hc₁ : s₁.regs 62 = c := by simp [s₁, hc']
    refine ⟨(rest', bs'', ns''), s₂, _, Exec.seq hx₁ hx₂, ⟨by rw [harr₂]; exact harr, ?_, ?_, ?_,
      ?_, by rw [h74₂, hc₁], fun r hr => ?_⟩, by simp; omega⟩
    · simpa using hB₁.of_arrs_eq harr₂ |>.of_arrs_eq rfl |> fun h => by
        rw [hregs₂ 67 (by omega) |>.symm] at h; exact h
    · exact (List.suffix_cons _ _).trans hbs
    · exact (List.suffix_append _ _).trans hns
    · rw [← htb]; simp [trimBlocks, hmin]
    · rw [hregs₂ r (by omega)]
      simp only [s₁, State.setReg_regs, show r ≠ 67 by omega, ↓reduceIte]
      exact hregs r hr
  have hI₀ : I (stack, bs, ns) s :=
    ⟨rfl, hB, List.suffix_refl _, List.suffix_refl _, rfl, h74, fun _ _ => rfl⟩
  obtain ⟨⟨rest, bs', ns'⟩, s', t, hx, ⟨harr, hB', hbs, hns, htb, h74', hregs⟩, hstop, ht⟩ :=
    Exec.while_pot I (fun g => 40 * g.1.length) hround _ s hI₀
  dsimp only at harr hB' hbs hns htb h74' hregs ht
  have hle := trimTestVal_le c rest
  have h0 : trimTestVal c rest = 0 := by
    rw [eval_reg (by omega)] at hstop
    rw [← h74']; simpa using hstop
  exact ⟨s', t, rest, bs', ns', hx, harr, hB', hbs, hns, htb, h0, by simpa using ht, hregs⟩

/-! ### The whole of `TRIM` -/

/-- Trim the block stack of the summary at register 57, which is not removed. -/
def trimBlocksProg : Cmd :=
  .seq (.assign 67 (.read Field.summaryTop.array (.reg 57)))
    (.seq trimTestProg'
      (.seq popLoopProg
        (.seq (.ite (.reg 67) trimTopProg .skip)
          (.write Field.summaryTop.array (.reg 57) (.reg 67)))))

/-- Part I, Section 5, `TRIM(S,c)`, with the record of `S` at register 57
(zero for the empty summary) and `c` in register 62. -/
def trimProg : Cmd :=
  .ite (.reg 57)
    (.seq (.assign 72 (.read Field.summaryLeast.array (.reg 57)))
      (.ite (.op .eq (.reg 72) (.reg 62)) (.assign 57 (.const 0)) trimBlocksProg))
    .skip

/-- The cells that `TRIM` may write: block records of the summary, and the top
pointer of its record. -/
def TrimCells (pS : ℕ) (bs : List ℕ) (a q : ℕ) : Prop :=
  IsBlockArr a ∧ q ∈ bs ∨ a = Field.summaryTop.array ∧ q = pS

theorem trimProg_regs : ∀ r : ℕ, r ∈ trimProg.writtenRegs → r = 57 ∨ (67 ≤ r ∧ r ≤ 74) := by
  decide

theorem trimBlocksProg_spec {w D M : ℕ} {s : State} {S : Summary} {bs ns : List ℕ}
    (hS : SummaryAt s M (s.regs 57) S bs ns) (hc : s.regs 62 ≤ D) (hW : Words D s)
    (hM : M ≤ D) (hD : D + 1 < 2 ^ w) :
    ∃ s' t bs' ns', Exec w trimBlocksProg s s' t ∧ Words D s' ∧
      (∀ r : ℕ, r < 67 ∨ 74 < r → s'.regs r = s.regs r) ∧
      Frame s s' (TrimCells (s.regs 57) bs) ∧
      SummaryAt s' M (s.regs 57) { S with blocks := trimBlocks (s.regs 62) S.blocks } bs' ns' ∧
      bs'.Sublist bs ∧ ns'.Sublist ns ∧
      t + 120 * (trimBlocks (s.regs 62) S.blocks).length +
        10 * stackNodes (trimBlocks (s.regs 62) S.blocks) ≤
        90 + 120 * S.blocks.length + 10 * stackNodes S.blocks := by
  set c := s.regs 62 with hcdef
  set pS := s.regs 57 with hpSdef
  obtain ⟨hpos, hcapS, hleast, fS, lS, topS, AS, stS, hSf, hSl, hStop, hAS, hBS, hns, hndS,
    hbndS⟩ := hS
  subst hns
  have hcap : 0 < M + 1 := by omega
  have htopD : topS ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hStop
  -- Load the stack and test its top block.
  let s₁ := s.setReg 67 topS
  have hx₁ : Exec w (.assign 67 (.read Field.summaryTop.array (.reg 57))) s s₁ 3 :=
    exec_ld (by omega) hStop (by omega)
  have hB₁ : BlockChain s₁ (M + 1) (s₁.regs 67) bs stS S.blocks := by
    simpa [s₁] using hBS.of_arrs_eq (s' := s₁) rfl
  obtain ⟨s₂, t₂, hx₂, ht₂, harr₂, h74₂, hregs₂⟩ :=
    trimTestProg'_spec (w := w) (D := D) hB₁ hW (by simp [s₁]; omega) hcap (by omega) (by omega)
  have hc₁ : s₁.regs 62 = c := by simp [s₁, hcdef]
  rw [hc₁] at h74₂
  have hc₂ : s₂.regs 62 = c := by rw [hregs₂ 62 (by omega), hc₁]
  have hB₂ : BlockChain s₂ (M + 1) (s₂.regs 67) bs stS S.blocks := by
    rw [hregs₂ 67 (by omega)]; exact hB₁.of_arrs_eq harr₂
  have hW₂ : Words D s₂ := hW.of_arrs_eq (by rw [harr₂]; rfl)
  -- The pop loop.
  obtain ⟨s₃, t₃, rest, bsr, nsr, hx₃, harr₃, hB₃, hbsr, hnsr, htb, h0, ht₃, hregs₃⟩ :=
    popLoopProg_spec (w := w) (D := D) hB₂ (by rw [hc₂, h74₂]) hW₂ (by omega) hcap (by omega)
      (by omega)
  rw [hc₂] at htb h0
  have hW₃ : Words D s₃ := hW₂.of_arrs_eq harr₃
  have ht₃pos := hx₃.time_pos
  have hrestle : rest.length ≤ S.blocks.length := by omega
  have hsn : stackNodes rest ≤ stackNodes S.blocks := by
    rw [← hB₃.nodes_length, ← hBS.nodes_length]; exact hnsr.length_le
  have hbsrnd : bsr.Nodup := hbndS.sublist hbsr.sublist
  have hc₃ : s₃.regs 62 = c := by rw [hregs₃ 62 (by omega), hc₂]
  -- Trim the lists of the new top block, if any.
  obtain ⟨s₄, t₄, ns₄, hx₄, ht₄, hB₄, hns₄, hF₄, hW₄, hregs₄⟩ : ∃ s₄ t₄ ns₄,
      Exec w (.ite (.reg 67) trimTopProg .skip) s₃ s₄ t₄ ∧
      t₄ + 120 * (trimBlocks c rest).length + 10 * stackNodes (trimBlocks c rest) ≤
        45 + 120 * rest.length + 10 * stackNodes rest ∧
      BlockChain s₄ (M + 1) (s₄.regs 67) bsr ns₄ (trimBlocks c rest) ∧ ns₄.Sublist nsr ∧
      Frame s₃ s₄ (fun a r => IsBlockArr a ∧ r ∈ bsr) ∧ Words D s₄ ∧
      (∀ r : ℕ, r < 68 ∨ 74 < r → s₄.regs r = s₃.regs r) := by
    obtain ⟨p, hp⟩ : ∃ p, s₃.regs 67 = p := ⟨_, rfl⟩
    have hB₃' := hB₃
    rw [hp] at hB₃'
    cases hB₃' with
    | nil =>
      refine ⟨s₃, _, [], exec_ite_zero hp (Exec.skip s₃), by simp [trimBlocks], ?_,
        List.Sublist.refl _, Frame.refl _ _, hW₃, fun _ _ => rfl⟩
      rw [hp]; exact .nil
    | @cons _ below lf ll rf rl bs'' ns'' L R q rest' hpos' hqc =>
      have hmin : q.minimum ≠ c := by
        intro h; simp [trimTestVal, h] at h0
      obtain ⟨s₄, t₄, ns₄, hx, ht, hB, hns, hF, hW', hregs⟩ :=
        trimTopProg_spec (w := w) (D := D) hB₃ hbsrnd hW₃ (by omega) hcap (by omega) (by omega)
      rw [hc₃] at ht hB
      have htb' : trimBlocks c (q :: rest') = trimTop c q :: rest' := by
        simp [trimBlocks, hmin]
      refine ⟨s₄, _, ns₄, exec_ite_pos (by omega : s₃.regs 67 ≠ 0) (by omega) hx, ?_, ?_, hns,
        hF.mono fun a r h => ⟨h.2, by rw [h.1, hp]; simp⟩, hW', hregs⟩
      swap
      · rw [htb']; exact hB
      rw [htb']
      simp only [List.length_cons, stackNodes] at ht ⊢
      omega
  rw [htb] at ht₄ hB₄
  -- Store the new top.
  have h57₄ : s₄.regs 57 = pS := by
    rw [hregs₄ 57 (by omega), hregs₃ 57 (by omega), hregs₂ 57 (by omega)]; simp [s₁, hpSdef]
  have hF₄' : Frame s s₄ (TrimCells pS bs) :=
    (((Frame.of_arrs_eq (s' := s₁) rfl (fun _ _ => False)).trans
      ((Frame.of_arrs_eq harr₂ (fun _ _ => False)).trans
        ((Frame.of_arrs_eq harr₃ (fun _ _ => False)).trans hF₄))).mono fun a r h => by
      rcases h with h | h | h | h
      · exact h.elim
      · exact h.elim
      · exact h.elim
      · exact Or.inl ⟨h.1, hbsr.subset h.2⟩)
  have hlen₄ : pS < (s₄.arrs Field.summaryTop.array).length := by
    rw [(hF₄' _).1]; exact (List.getElem?_eq_some_iff.mp hStop).1
  have h67₄ := hB₄.top_lt hcap
  have hx₅ := exec_st (w := w) (s := s₄) (a := Field.summaryTop.array) (idx := 57) (val := 67)
    (by rw [h57₄]; exact hlen₄) (by rw [h57₄]; omega) (by omega)
  rw [h57₄] at hx₅
  have hFw := Frame.writeArr s₄ Field.summaryTop.array pS (s₄.regs 67)
  have hF₅ : Frame s (s₄.writeArr Field.summaryTop.array pS (s₄.regs 67)) (TrimCells pS bs) :=
    (hF₄'.trans hFw).mono fun a r h => by
      rcases h with h | h
      · exact h
      · exact Or.inr h
  have hx := Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ hx₅)))
  have hnode : ∀ r, ¬ NodeCell (TrimCells pS bs) r := by
    intro r; simp [NodeCell, TrimCells, IsBlockArr, Field.array]
  refine ⟨_, _, bsr, AS ++ ns₄, hx, hW₄.writeArr _ _ (by omega), fun r hr => ?_, hF₅,
    ⟨hpos, hcapS, ?_, fS, lS, s₄.regs 67, AS, ns₄, ?_, ?_, ?_, hAS.frame hF₅ fun r _ => hnode r,
      ?_, rfl, ?_, hbsrnd⟩, hbsr.sublist, ?_, ?_⟩
  · simp only [State.writeArr_regs]
    rw [hregs₄ r (by omega), hregs₃ r hr, hregs₂ r (by omega)]
    simp [s₁, show r ≠ 67 by omega]
  · rw [hF₅.get (by simp [TrimCells, IsBlockArr, Field.array])]; exact hleast
  · rw [hF₅.get (by simp [TrimCells, IsBlockArr, Field.array])]; exact hSf
  · rw [hF₅.get (by simp [TrimCells, IsBlockArr, Field.array])]; exact hSl
  · exact writeArr_get_self hlen₄
  · exact hB₄.frame hFw (fun r _ => by simp [BlockCell, Field.array])
      (fun r _ => by simp [NodeCell, Field.array])
  · exact (List.nodup_append.mp hndS |> fun h =>
      List.nodup_append.mpr ⟨h.1, h.2.1.sublist (hns₄.trans hnsr.sublist),
        fun a ha b hb e => h.2.2 a ha b ((hns₄.trans hnsr.sublist).subset hb) e⟩) |>.sublist
      (List.Sublist.refl _)
  · exact (List.Sublist.refl AS).append (hns₄.trans hnsr.sublist)
  · omega

/-- `TRIM` refines `trim`. It writes only block records of the summary and
the top pointer of its record, keeps a sublist of its blocks and returns, and
costs at most 100 steps plus the weight it removes. -/
theorem trimProg_spec {w D M : ℕ} {s : State} {o : Option Summary} {bs ns : List ℕ}
    (hS : OptSummaryAt s M (s.regs 57) o bs ns) (hc : s.regs 62 ≤ D) (hW : Words D s)
    (hM : M ≤ D) (hD : D + 1 < 2 ^ w) :
    ∃ s' t bs' ns', Exec w trimProg s s' t ∧ Words D s' ∧
      (∀ r : ℕ, r ≠ 57 → r < 67 ∨ 74 < r → s'.regs r = s.regs r) ∧
      Frame s s' (TrimCells (s.regs 57) bs) ∧
      (s'.regs 57 = s.regs 57 ∨ s'.regs 57 = 0) ∧
      OptSummaryAt s' M (s'.regs 57) (trim o (s.regs 62)) bs' ns' ∧
      bs'.Sublist bs ∧ ns'.Sublist ns ∧
      t + weight (trim o (s.regs 62)) ≤ 100 + weight o := by
  cases o with
  | none =>
    obtain ⟨h57, rfl, rfl⟩ := hS
    refine ⟨s, _, [], [], exec_ite_zero h57 (Exec.skip s), hW, fun _ _ _ => rfl, Frame.refl _ _,
      Or.inl rfl, ⟨h57, rfl, rfl⟩, List.Sublist.refl _, List.Sublist.refl _, by simp [trim, weight]⟩
  | some S =>
    simp only [OptSummaryAt] at hS
    have hp := hS.ptr_pos
    have hleast : (s.arrs Field.summaryLeast.array)[s.regs 57]? = some S.least := hS.2.2.1
    have hlD : S.least ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hleast
    let s₁ := s.setReg 72 S.least
    have hx₁ : Exec w (.assign 72 (.read Field.summaryLeast.array (.reg 57))) s s₁ 3 :=
      exec_ld (by omega) hleast (by omega)
    have heq : (Expr.op .eq (.reg 72) (.reg 62)).eval w s₁ =
        some (if S.least = s.regs 62 then 1 else 0) := by
      rw [eval_op (eval_reg (by simp [s₁]; omega)) (eval_reg (by simp [s₁]; omega)),
        binop_eq (by omega)]
      simp [s₁]
    have hcost : (Expr.op .eq (.reg 72) (.reg 62)).cost = 3 := rfl
    by_cases hl : S.least = s.regs 62
    · have htrim : trim (some S) (s.regs 62) = none := by simp [trim, hl]
      have hx := exec_ite_pos (c₂ := .skip) (by omega : s.regs 57 ≠ 0) (by omega)
        (Exec.seq hx₁ (exec_ite_eval (c₂ := trimBlocksProg) heq
          (fun _ => exec_setc (s := s₁) (dst := 57) (n := 0) (by omega))
          (fun h => by simp [hl] at h)))
      rw [htrim]
      refine ⟨_, _, [], [], hx, hW, fun r h1 h2 => ?_, Frame.of_arrs_eq rfl _, Or.inr (by simp),
        ⟨by simp, rfl, rfl⟩, List.nil_sublist _, List.nil_sublist _, by simp [weight]; omega⟩
      simp [s₁, h1, show r ≠ 72 by omega]
    · have htrim : trim (some S) (s.regs 62) =
          some { S with blocks := trimBlocks (s.regs 62) S.blocks } := by simp [trim, hl]
      have hS₁ : SummaryAt s₁ M (s₁.regs 57) S bs ns := by
        simpa [s₁] using hS.of_arrs_eq (s' := s₁) rfl
      obtain ⟨s₂, t₂, bs', ns', hx₂, hW₂, hregs₂, hF₂, hS₂, hbs, hns, ht₂⟩ :=
        trimBlocksProg_spec (w := w) (D := D) hS₁ (by simp [s₁]; omega) hW hM hD
      have h57₁ : s₁.regs 57 = s.regs 57 := by simp [s₁]
      have h62₁ : s₁.regs 62 = s.regs 62 := by simp [s₁]
      rw [h57₁] at hF₂ hS₂
      rw [h62₁] at hS₂ ht₂
      have hx := exec_ite_pos (c₂ := .skip) (by omega : s.regs 57 ≠ 0) (by omega)
        (Exec.seq hx₁ (exec_ite_eval (c₁ := .assign 57 (.const 0)) heq
          (fun h => by simp [hl] at h) (fun _ => hx₂)))
      have h57₂ : s₂.regs 57 = s.regs 57 := by rw [hregs₂ 57 (by omega), h57₁]
      rw [htrim]
      refine ⟨s₂, _, bs', ns', hx, hW₂, fun r h1 h2 => ?_, hF₂.mono fun a q h => h,
        Or.inl h57₂, by rw [h57₂]; exact hS₂, hbs, hns, ?_⟩
      · rw [hregs₂ r h2]; simp [s₁, show r ≠ 72 by omega]
      · simp only [weight, nodeCount]
        rw [hcost]
        omega

end GraphMinor.Compute.PlanarityRam
