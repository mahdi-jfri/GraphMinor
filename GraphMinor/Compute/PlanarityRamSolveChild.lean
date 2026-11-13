module

public import GraphMinor.Compute.PlanarityRamSolveList
import GraphMinor.Compute.WhileRounds

/-!
# The first loop of `MERGE`: emptying the child's block stack

Part I, Section 4 of the planarity note starts `MERGE(S,T)` with

    while T.P is not empty:
        Q := pop(T.P)
        if Q.L and Q.R are both nonempty: reject the graph
        append the nonempty side of Q to R

This is `mergeChild` of `Algorithm.lean`. Here the RAM loop `childLoopProg`
does it with the block pointer in register 67 and the header of `R` in
registers 63 and 64. A rejection writes zero to register 35 and leaves the
loop. The main result is `childLoopProg_spec`: the loop refines `mergeChild`,
writes only next pointers of the nodes involved, and costs at most 25 steps
per block plus 26.

Registers 68 to 71 receive the four list headers of the popped block
(`loadBlockProg`).
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- A block stack depends only on the arrays of the state. -/
theorem BlockChain.of_arrs_eq {s s' : State} {cap p : ℕ} {bs ns : List ℕ} {stack : List Block}
    (h : BlockChain s cap p bs ns stack) (he : s'.arrs = s.arrs) :
    BlockChain s' cap p bs ns stack :=
  h.frame (Frame.of_arrs_eq he (fun _ _ => False)) (fun _ _ => by simp [BlockCell])
    (fun _ _ => by simp [NodeCell])

/-- A summary depends only on the arrays of the state. -/
theorem SummaryAt.of_arrs_eq {s s' : State} {M p : ℕ} {S : Summary} {bs ns : List ℕ}
    (h : SummaryAt s M p S bs ns) (he : s'.arrs = s.arrs) : SummaryAt s' M p S bs ns :=
  h.frame (Frame.of_arrs_eq he (fun _ _ => False)) (by simp [SummaryCell])
    (fun _ _ => by simp [BlockCell]) (fun _ _ => by simp [NodeCell])

/-- A frame extends to a later state with the same arrays. -/
theorem Frame.of_arrs_eq_right {s₀ s s' : State} {W : ℕ → ℕ → Prop} (h : Frame s₀ s W)
    (he : s'.arrs = s.arrs) : Frame s₀ s' W := by
  intro a
  rw [he]
  exact h a

/-- Registers 68 to 71 receive the headers of the block whose address is in
register 67. -/
def loadBlockProg : Cmd :=
  .seq (.assign 68 (.read Field.blockLeftFirst.array (.reg 67)))
    (.seq (.assign 69 (.read Field.blockLeftLast.array (.reg 67)))
      (.seq (.assign 70 (.read Field.blockRightFirst.array (.reg 67)))
        (.assign 71 (.read Field.blockRightLast.array (.reg 67)))))

/-- Register 67 follows the below pointer of its block. -/
def popProg : Cmd := .assign 67 (.read Field.blockBelow.array (.reg 67))

/-- The four headers of the top block, loaded in 12 steps. -/
theorem loadBlockProg_exec {w : ℕ} {s : State} {lf ll rf rl : ℕ} (hq : s.regs 67 < 2 ^ w)
    (hlf : (s.arrs Field.blockLeftFirst.array)[s.regs 67]? = some lf)
    (hll : (s.arrs Field.blockLeftLast.array)[s.regs 67]? = some ll)
    (hrf : (s.arrs Field.blockRightFirst.array)[s.regs 67]? = some rf)
    (hrl : (s.arrs Field.blockRightLast.array)[s.regs 67]? = some rl)
    (hw : lf < 2 ^ w ∧ ll < 2 ^ w ∧ rf < 2 ^ w ∧ rl < 2 ^ w) :
    Exec w loadBlockProg s
      ((((s.setReg 68 lf).setReg 69 ll).setReg 70 rf).setReg 71 rl) 12 :=
  Exec.seq (exec_ld hq hlf hw.1)
    (Exec.seq (exec_ld (by simpa using hq) (by simpa using hll) hw.2.1)
      (Exec.seq (exec_ld (by simpa using hq) (by simpa using hrf) hw.2.2.1)
        (exec_ld (by simpa using hq) (by simpa using hrl) hw.2.2.2)))

/-- One round of the child loop. -/
def childBodyProg : Cmd :=
  .seq loadBlockProg
    (.ite (.reg 68)
      (.ite (.reg 70) (.seq (.assign 35 (.const 0)) (.assign 67 (.const 0)))
        (.seq (appendProg 63 64 68 69) popProg))
      (.seq (appendProg 63 64 70 71) popProg))

/-- The child loop. -/
def childLoopProg : Cmd := .while (.reg 67) childBodyProg

/-- The state of the child loop: the blocks still on the stack, the list `R`
built so far, its addresses, and the block and node addresses of the stack.
`none` records a rejection. -/
abbrev ChildGhost := Option (List Block × List ReturnNode × List ℕ × List ℕ × List ℕ)

/-- The invariant of the child loop, for a start state `s₀` whose stack has
blocks `blocks₀` and node addresses `ns₀` and whose list `R` has addresses
`RA₀` and contents `right₀`. -/
def ChildInv (D cap : ℕ) (s₀ : State) (blocks₀ : List Block) (right₀ : List ReturnNode)
    (RA₀ ns₀ : List ℕ) : ChildGhost → State → Prop
  | none, s => Frame s₀ s (fun a q => a = Field.nodeNext.array ∧ q ∈ RA₀ ++ ns₀) ∧
      Words D s ∧ s.regs 35 = 0 ∧ s.regs 67 = 0 ∧ mergeChild blocks₀ right₀ = none
  | some (rest, right, RA, bs, ns), s =>
      Frame s₀ s (fun a q => a = Field.nodeNext.array ∧ q ∈ RA₀ ++ ns₀) ∧
      Words D s ∧ s.regs 35 = 1 ∧ BlockChain s cap (s.regs 67) bs ns rest ∧
      ListAt s cap (s.regs 63) (s.regs 64) RA right ∧ RA ++ ns = RA₀ ++ ns₀ ∧
      mergeChild blocks₀ right₀ = mergeChild rest right

/-- Twenty-five steps per remaining block, one more for the last test. -/
def childPot : ChildGhost → ℕ
  | none => 0
  | some (rest, _, _, _, _) => 25 * (rest.length + 1)

private theorem list_empty_of_first {s : State} {cap f l : ℕ} {A : List ℕ}
    {x : List ReturnNode} (h : ListAt s cap f l A x) (hf : f = 0) : A = [] ∧ x = [] := by
  have hA := h.first_eq_zero_iff.mp hf
  have := h.1.length_eq
  rw [hA] at this
  exact ⟨hA, List.length_eq_zero_iff.mp this.symm⟩

private theorem list_ne_of_first {s : State} {cap f l : ℕ} {A : List ℕ}
    {x : List ReturnNode} (h : ListAt s cap f l A x) (hf : f ≠ 0) : x ≠ [] := by
  intro hx
  apply hf
  rw [h.1.first_eq_zero_iff]
  exact hx

/-- One round of the child loop keeps its invariant and pays for itself. -/
theorem childLoop_round {w D cap : ℕ} {s₀ : State} {blocks₀ : List Block}
    {right₀ : List ReturnNode} {RA₀ ns₀ : List ℕ} (hnd₀ : (RA₀ ++ ns₀).Nodup)
    (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) :
    ∀ g s, ChildInv D cap s₀ blocks₀ right₀ RA₀ ns₀ g s →
      ∃ v, (Expr.reg 67).eval w s = some v ∧ (v ≠ 0 →
        ∃ g' s' t, Exec w childBodyProg s s' t ∧ ChildInv D cap s₀ blocks₀ right₀ RA₀ ns₀ g' s' ∧
          (Expr.reg 67).cost + t + childPot g' ≤ childPot g) := by
  rintro (_ | ⟨rest, right, RA, bs, ns⟩) s hI
  · obtain ⟨-, -, -, h67, -⟩ := hI
    refine ⟨0, eval_reg (by rw [h67]; exact Nat.pow_pos (by decide)) |>.trans (by rw [h67]),
      fun h => absurd rfl h⟩
  obtain ⟨hF, hW, h35, hB, hR, hns, heq⟩ := hI
  have hqcap : s.regs 67 < cap := by
    rcases Nat.eq_zero_or_pos (s.regs 67) with h | h
    · rw [h]; exact hcap
    · cases rest with
      | nil => exact absurd ((hB.top_eq_zero_iff).mpr rfl) (by omega)
      | cons _ _ =>
        obtain ⟨q, hq⟩ : ∃ q, s.regs 67 = q := ⟨_, rfl⟩
        rw [hq] at hB ⊢
        cases hB with
        | cons _ hb _ _ _ _ _ _ _ _ => exact hb
  have hqw : s.regs 67 < 2 ^ w := by omega
  refine ⟨_, eval_reg hqw, fun hv => ?_⟩
  -- A nonzero top pointer means a nonempty stack.
  obtain ⟨q, hq⟩ : ∃ q, s.regs 67 = q := ⟨_, rfl⟩
  rw [hq] at hB
  cases hB with
  | nil => exact absurd hq hv
  | @cons _ below lf ll rf rl bs' ns' L R blk rest' hpos hqc hlf hll hrf hrl hbelow hL hR' hrest =>
    rw [← hq] at hlf hll hrf hrl hbelow
    have hpL := hL.pointers_lt hcap
    have hpR := hR'.pointers_lt hcap
    have hbelowD : below ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hbelow
    let s₁ := (((s.setReg 68 lf).setReg 69 ll).setReg 70 rf).setReg 71 rl
    have hx₁ : Exec w loadBlockProg s s₁ 12 :=
      loadBlockProg_exec hqw hlf hll hrf hrl ⟨by omega, by omega, by omega, by omega⟩
    have harr₁ : s₁.arrs = s.arrs := rfl
    have hL₁ : ListAt s₁ cap (s₁.regs 68) (s₁.regs 69) L blk.left := by
      simpa [s₁] using hL.of_arrs_eq harr₁
    have hRR₁ : ListAt s₁ cap (s₁.regs 70) (s₁.regs 71) R blk.right := by
      simpa [s₁] using hR'.of_arrs_eq harr₁
    have hR₁ : ListAt s₁ cap (s₁.regs 63) (s₁.regs 64) RA right := by
      simpa [s₁] using hR.of_arrs_eq harr₁
    have hrest₁ : BlockChain s₁ cap below bs' ns' rest' := hrest.of_arrs_eq harr₁
    have hnd : (RA ++ (L ++ R ++ ns')).Nodup := by rw [hns]; exact hnd₀
    have hW₁ : Words D s₁ := hW
    have h35₁ : s₁.regs 35 = 1 := by simpa [s₁] using h35
    have h67₁ : s₁.regs 67 = q := by simpa [s₁] using hq
    by_cases hlf0 : lf = 0
    · -- The left side is empty: append the right side.
      obtain ⟨hL0, hx0⟩ := list_empty_of_first hL hlf0
      subst hL0
      have hdis : ∀ a ∈ RA, a ∉ R := fun a ha hb => by
        have := List.nodup_append.mp hnd
        exact this.2.2 a ha a (by simp [hb]) rfl
      obtain ⟨s₂, t₂, hx₂, ht₂, hR₂, hF₂, hregs₂, hW₂⟩ :=
        appendProg_spec (fA := 63) (lA := 64) (fB := 70) (lB := 71) (by decide) (by decide)
          hR₁ hRR₁ hdis hcap hcapD hD hW₁
      have hq₂ : s₂.regs 67 = q := by rw [hregs₂ 67 (by decide) (by decide), h67₁]
      have hbelow₂ : (s₂.arrs Field.blockBelow.array)[s₂.regs 67]? = some below := by
        rw [hq₂, hF₂.get (by simp [Field.array]), harr₁, ← hq]
        exact hbelow
      let s₃ := s₂.setReg 67 below
      refine ⟨some (rest', right ++ blk.right, RA ++ R, bs', ns'), s₃, 12 + (1 + (t₂ + 3)),
        Exec.seq hx₁ (exec_ite_zero (by simpa [s₁] using hlf0)
          (Exec.seq hx₂ (exec_ld (by omega) hbelow₂ (by omega)))), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · refine ((hF.of_arrs_eq_right harr₁).trans (hF₂.trans (Frame.setReg s₂ 67 below
          (fun _ _ => False)))).mono ?_
        intro a b hab
        rcases hab with h | (h | h)
        · exact h
        · exact ⟨h.1, by rw [← hns]; exact List.mem_append_left _ h.2⟩
        · exact h.elim
      · exact hW₂.setReg _ _
      · simp [s₃, hregs₂ 35 (by decide) (by decide), h35₁]
      · simpa [s₃] using (hrest₁.frame hF₂ (fun _ _ => by simp [BlockCell, Field.array])
          (fun a ha => by
            simp only [NodeCell, Field.array, not_or]
            refine ⟨by omega, by omega, fun h => ?_⟩
            have := List.nodup_append.mp hnd
            exact this.2.2 _ h.2 a (by simp [ha]) rfl)).of_arrs_eq (s' := s₃) rfl
      · simpa [s₃] using hR₂.of_arrs_eq (s' := s₃) rfl
      · simp [← hns]
      · rw [heq]
        simp [mergeChild, list_empty_of_first hL hlf0 |>.2]
      · simp [childPot]
        omega
    · by_cases hrf0 : rf = 0
      · -- The right side is empty: append the left side.
        obtain ⟨hR0, hy0⟩ := list_empty_of_first hR' hrf0
        subst hR0
        have hdis : ∀ a ∈ RA, a ∉ L := fun a ha hb => by
          have := List.nodup_append.mp hnd
          exact this.2.2 a ha a (by simp [hb]) rfl
        obtain ⟨s₂, t₂, hx₂, ht₂, hR₂, hF₂, hregs₂, hW₂⟩ :=
          appendProg_spec (fA := 63) (lA := 64) (fB := 68) (lB := 69) (by decide) (by decide)
            hR₁ hL₁ hdis hcap hcapD hD hW₁
        have hq₂ : s₂.regs 67 = q := by rw [hregs₂ 67 (by decide) (by decide), h67₁]
        have hbelow₂ : (s₂.arrs Field.blockBelow.array)[s₂.regs 67]? = some below := by
          rw [hq₂, hF₂.get (by simp [Field.array]), harr₁, ← hq]
          exact hbelow
        let s₃ := s₂.setReg 67 below
        refine ⟨some (rest', right ++ blk.left, RA ++ L, bs', ns'), s₃, 12 + (1 + (1 + (t₂ + 3))),
          Exec.seq hx₁ (exec_ite_pos (by simpa [s₁] using hlf0) (by simp [s₁]; omega)
            (exec_ite_zero (by simpa [s₁] using hrf0)
              (Exec.seq hx₂ (exec_ld (by omega) hbelow₂ (by omega))))),
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · refine ((hF.of_arrs_eq_right harr₁).trans (hF₂.trans (Frame.setReg s₂ 67 below
            (fun _ _ => False)))).mono ?_
          intro a b hab
          rcases hab with h | (h | h)
          · exact h
          · exact ⟨h.1, by rw [← hns]; exact List.mem_append_left _ h.2⟩
          · exact h.elim
        · exact hW₂.setReg _ _
        · simp [s₃, hregs₂ 35 (by decide) (by decide), h35₁]
        · simpa [s₃] using (hrest₁.frame hF₂ (fun _ _ => by simp [BlockCell, Field.array])
            (fun a ha => by
              simp only [NodeCell, Field.array, not_or]
              refine ⟨by omega, by omega, fun h => ?_⟩
              have := List.nodup_append.mp hnd
              exact this.2.2 _ h.2 a (by simp [ha]) rfl)).of_arrs_eq (s' := s₃) rfl
        · simpa [s₃] using hR₂.of_arrs_eq (s' := s₃) rfl
        · simp [← hns]
        · rw [heq]
          have hxne := list_ne_of_first hL hlf0
          simp [mergeChild, hy0, hxne]
        · simp [childPot]
          omega
      · -- Both sides are nonempty: reject.
        let s₂ := (s₁.setReg 35 0).setReg 67 0
        refine ⟨none, s₂, 12 + (1 + (1 + (2 + 2))),
          Exec.seq hx₁ (exec_ite_pos (by simpa [s₁] using hlf0) (by simp [s₁]; omega)
            (exec_ite_pos (by simpa [s₁] using hrf0) (by simp [s₁]; omega)
              (Exec.seq (exec_setc (by omega)) (exec_setc (by omega))))), ⟨?_, hW₁, ?_, ?_, ?_⟩, ?_⟩
        · exact hF.of_arrs_eq_right rfl
        · simp [s₂]
        · simp [s₂]
        · rw [heq]
          simp [mergeChild, list_ne_of_first hL hlf0, list_ne_of_first hR' hrf0]
        · simp only [childPot, List.length_cons, Expr.cost_reg]
          omega

/-- Part I, Section 4, the loop over the child's stack in `MERGE`. Starting
with 1 in register 35, a stack at register 67 and a list `R` at registers 63
and 64, the loop ends either with 0 in register 35 when `mergeChild` rejects,
or with `R` holding the result of `mergeChild`, whose addresses are those of
`R` followed by the node addresses of the stack. It writes only next pointers
of these nodes, and costs at most `25 * (blocks + 1) + 1` steps. -/
theorem childLoopProg_spec {w D cap : ℕ} {s : State} {blocks : List Block}
    {right : List ReturnNode} {RA bs ns : List ℕ}
    (hB : BlockChain s cap (s.regs 67) bs ns blocks)
    (hR : ListAt s cap (s.regs 63) (s.regs 64) RA right) (hnd : (RA ++ ns).Nodup)
    (h35 : s.regs 35 = 1) (hW : Words D s)
    (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) :
    ∃ s' t, Exec w childLoopProg s s' t ∧ t ≤ 25 * (blocks.length + 1) + 1 ∧
      Frame s s' (fun a q => a = Field.nodeNext.array ∧ q ∈ RA ++ ns) ∧ Words D s' ∧
      (∀ r, r ∉ childLoopProg.writtenRegs → s'.regs r = s.regs r) ∧
      match mergeChild blocks right with
      | none => s'.regs 35 = 0
      | some right' => s'.regs 35 = 1 ∧ ListAt s' cap (s'.regs 63) (s'.regs 64) (RA ++ ns) right' := by
  have hI₀ : ChildInv D cap s blocks right RA ns (some (blocks, right, RA, bs, ns)) s :=
    ⟨Frame.refl s _, hW, h35, hB, hR, rfl, rfl⟩
  obtain ⟨g, s', t, hx, hI, hstop, ht⟩ :=
    Exec.while_pot (ChildInv D cap s blocks right RA ns) childPot
      (childLoop_round hnd hcap hcapD hD) _ s hI₀
  refine ⟨s', t, hx, ?_, ?_, ?_, fun r hr => hx.regs_eq_of_not_mem_writtenRegs hr, ?_⟩
  · simp [childPot] at ht
    omega
  · rcases g with _ | ⟨rest, right', RA', bs', ns'⟩
    · exact hI.1
    · exact hI.1
  · rcases g with _ | ⟨rest, right', RA', bs', ns'⟩
    · exact hI.2.1
    · exact hI.2.1
  · rcases g with _ | ⟨rest, right', RA', bs', ns'⟩
    · obtain ⟨-, -, h35', -, heq⟩ := hI
      rw [heq]
      exact h35'
    · obtain ⟨-, -, h35', hB', hR', hns, heq⟩ := hI
      -- The loop stopped, so the stack is empty.
      have h67 : s'.regs 67 = 0 := by
        have hp := hB'.top_eq_zero_iff
        by_contra hne
        have hlt : s'.regs 67 < 2 ^ w := by
          rcases rest with _ | ⟨b, rest⟩
          · exact absurd (hp.mpr rfl) hne
          · obtain ⟨q, hq⟩ : ∃ q, s'.regs 67 = q := ⟨_, rfl⟩
            rw [hq] at hB' ⊢
            cases hB' with
            | cons _ hb _ _ _ _ _ _ _ _ => omega
        have := (eval_reg (s := s') (r := 67) hlt).symm.trans hstop
        simp at this
        exact hne this
      have hrest : rest = [] := hB'.top_eq_zero_iff.mp h67
      subst hrest
      have hns' : ns' = [] := by rw [h67] at hB'; cases hB'; rfl
      subst hns'
      rw [heq]
      simp only [mergeChild]
      exact ⟨h35', by simpa [← hns] using hR'⟩

end GraphMinor.Compute.PlanarityRam
