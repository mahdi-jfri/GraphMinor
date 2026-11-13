module

public import GraphMinor.Compute.PlanarityRamSolveChild
import GraphMinor.Compute.WhileRounds

/-!
# The second loop of `MERGE`: popping the old blocks above the new minimum

Part I, Section 4 of the planarity note continues `MERGE(S,T)` with

    while S.P is not empty and max(top(S.P)) > b:
        Q := pop(S.P)
        if max(Q.R)>b: swap Q.L and Q.R
        if max(Q.R)>b: reject the graph
        append Q.L to L
        append Q.R to R

This is `mergeOld` of `Algorithm.lean`. The RAM loop `oldLoopProg` keeps the
stack pointer in register 67, `b` in register 62, and the headers of `L` and
`R` in registers 65, 66 and 63, 64. Register 74 holds the loop test. A
rejection writes zero to register 35 and leaves the loop.

The main result is `oldLoopProg_spec`: the loop refines `mergeOld`, writes
only next pointers of the nodes involved, and costs a constant plus a
constant per popped block.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The test `b + 1 < r`, where register 62 holds `b`. -/
def gtExpr (r : ℕ) : Expr := .op .lt (.op .add (.reg 62) (.const 1)) (.reg r)

theorem gtExpr_eval {w : ℕ} {s : State} {r : ℕ} (hw : 1 < 2 ^ w)
    (h62 : s.regs 62 + 1 < 2 ^ w) (hr : s.regs r < 2 ^ w) :
    (gtExpr r).eval w s = some (if s.regs 62 + 1 < s.regs r then 1 else 0) := by
  unfold gtExpr
  rw [eval_op (eval_op (eval_reg (by omega)) (eval_const hw) |>.trans (binop_add h62))
    (eval_reg hr), binop_lt hw]

theorem exec_ite_eval {w : ℕ} {s s' : State} {cond : Expr} {c₁ c₂ : Cmd} {v t : ℕ}
    (hc : cond.eval w s = some v) (h₁ : v ≠ 0 → Exec w c₁ s s' t)
    (h₂ : v = 0 → Exec w c₂ s s' t) : Exec w (.ite cond c₁ c₂) s s' (cond.cost + t) := by
  by_cases hv : v = 0
  · subst hv
    exact Exec.ite_false hc (h₂ rfl)
  · exact Exec.ite_true hc hv (h₁ hv)

/-- The loop test: the number of sides of the top block whose maximum
exceeds `b`, or zero for the empty stack. -/
def oldTestVal (b : ℕ) : List Block → ℕ
  | [] => 0
  | q :: _ => (if b + 1 < maxTag q.left then 1 else 0) + (if b + 1 < maxTag q.right then 1 else 0)

theorem oldTestVal_cons_ne_zero (b : ℕ) (q : Block) (rest : List Block) :
    oldTestVal b (q :: rest) ≠ 0 ↔ q.maximum > (b : Int) := by
  have h1 := listMaximum_gt_iff q.left b
  have h2 := listMaximum_gt_iff q.right b
  rw [gt_iff_lt] at h1 h2
  simp only [oldTestVal, Block.maximum, gt_iff_lt, lt_max_iff]
  rw [h1, h2]
  split_ifs <;> simp_all

/-- A tag read from memory is at most `D + 1`. -/
theorem ListAt.maxTag_le {s : State} {cap f l D : ℕ} {A : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x) (hW : Words D s) : maxTag x ≤ D + 1 := by
  cases x with
  | nil => simp [maxTag]
  | cons b x =>
    have := hW.get (by simp [Field.array]) (by simp [Field.array]) h.first_depth
    simp only [maxTag]
    omega

/-- `74 := oldTestVal b` of the stack at register 67. -/
def oldTestProg : Cmd :=
  .ite (.reg 67)
    (.seq (.assign 68 (.read Field.blockLeftFirst.array (.reg 67)))
      (.seq (.assign 70 (.read Field.blockRightFirst.array (.reg 67)))
        (.seq (maxTagProg 72 68)
          (.seq (maxTagProg 73 70)
            (.assign 74 (.op .add (gtExpr 72) (gtExpr 73)))))))
    (.assign 74 (.const 0))

theorem oldTestProg_spec {w D cap : ℕ} {s : State} {bs ns : List ℕ} {stack : List Block}
    (hB : BlockChain s cap (s.regs 67) bs ns stack) (hW : Words D s) (h62 : s.regs 62 ≤ D)
    (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 2 < 2 ^ w) :
    ∃ s' t, Exec w oldTestProg s s' t ∧ t ≤ 40 ∧ s'.arrs = s.arrs ∧
      s'.regs 74 = oldTestVal (s.regs 62) stack ∧
      (∀ r, r ∉ oldTestProg.writtenRegs → s'.regs r = s.regs r) := by
  obtain ⟨q, hq⟩ : ∃ q, s.regs 67 = q := ⟨_, rfl⟩
  rw [hq] at hB
  cases hB with
  | nil =>
    refine ⟨_, _, exec_ite_zero hq (exec_setc (by omega)), by omega, rfl, by simp [oldTestVal],
      fun r hr => ?_⟩
    simp only [oldTestProg, maxTagProg, Cmd.writtenRegs, Finset.mem_union,
      Finset.mem_singleton, not_or] at hr
    simp [hr]
  | @cons _ below lf ll rf rl bs' ns' L R blk rest hpos hqc hlf _ hrf _ _ hL hR _ =>
    rw [← hq] at hlf hrf
    have hqw : s.regs 67 < 2 ^ w := by omega
    have hpL := hL.pointers_lt hcap
    have hpR := hR.pointers_lt hcap
    let s₁ := s.setReg 68 lf
    let s₂ := s₁.setReg 70 rf
    have hL₂ : ListAt s₂ cap (s₂.regs 68) ll L blk.left := by
      simpa [s₂, s₁] using hL.of_arrs_eq (s' := s₂) rfl
    have hR₂ : ListAt s₂ cap (s₂.regs 70) rl R blk.right := by
      simpa [s₂, s₁] using hR.of_arrs_eq (s' := s₂) rfl
    obtain ⟨t₃, hx₃, ht₃⟩ := maxTagProg_spec (w := w) (D := D) (dst := 72) hL₂ hcap hcapD (by omega) hW
    let s₃ := s₂.setReg 72 (maxTag blk.left)
    have hR₃ : ListAt s₃ cap (s₃.regs 70) rl R blk.right := by
      simpa [s₃] using hR₂.of_arrs_eq (s' := s₃) rfl
    obtain ⟨t₄, hx₄, ht₄⟩ := maxTagProg_spec (w := w) (D := D) (s := s₃) (dst := 73) hR₃ hcap hcapD (by omega) hW
    let s₄ := s₃.setReg 73 (maxTag blk.right)
    have htagL : maxTag blk.left ≤ D + 1 := hL.maxTag_le hW
    have htagR : maxTag blk.right ≤ D + 1 := hR.maxTag_le hW
    have h62₄ : s₄.regs 62 = s.regs 62 := by simp [s₄, s₃, s₂, s₁]
    have h72 : s₄.regs 72 = maxTag blk.left := by simp [s₄, s₃]
    have h73 : s₄.regs 73 = maxTag blk.right := by simp [s₄]
    have he : (Expr.op .add (gtExpr 72) (gtExpr 73)).eval w s₄ =
        some (oldTestVal (s.regs 62) (blk :: rest)) := by
      rw [eval_op (gtExpr_eval (by omega) (by rw [h62₄]; omega) (by rw [h72]; omega))
        (gtExpr_eval (by omega) (by rw [h62₄]; omega) (by rw [h73]; omega)), binop_add
        (by split_ifs <;> omega), h62₄, h72, h73]
      rfl
    refine ⟨s₄.setReg 74 _, _, exec_ite_pos (by omega) hqw
      (Exec.seq (exec_ld hqw hlf (by omega)) (Exec.seq (exec_ld (by simpa [s₁] using hqw)
        (by simpa [s₁] using hrf) (by omega)) (Exec.seq hx₃ (Exec.seq hx₄ (Exec.assign he))))),
      by
        have : (Expr.op .add (gtExpr 72) (gtExpr 73)).cost = 11 := rfl
        omega, rfl, by simp, fun r hr => ?_⟩
    simp only [oldTestProg, maxTagProg, Cmd.writtenRegs, Finset.mem_union,
      Finset.mem_singleton, not_or] at hr
    simp [s₄, s₃, s₂, s₁, hr]

/-- A list survives the writes of an append to other nodes. -/
theorem ListAt.frame_next {s s' : State} {cap f l : ℕ} {A B : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x)
    (hF : Frame s s' (fun a q => a = Field.nodeNext.array ∧ q ∈ B))
    (hdis : ∀ q ∈ A, q ∉ B) : ListAt s' cap f l A x :=
  h.frame hF fun q hq => by
    simp only [NodeCell, Field.array, not_or]
    exact ⟨by omega, by omega, fun h => hdis q hq h.2⟩

/-- A block stack survives the writes of an append to other nodes. -/
theorem BlockChain.frame_next {s s' : State} {cap p : ℕ} {bs ns B : List ℕ} {stack : List Block}
    (h : BlockChain s cap p bs ns stack)
    (hF : Frame s s' (fun a q => a = Field.nodeNext.array ∧ q ∈ B))
    (hdis : ∀ q ∈ ns, q ∉ B) : BlockChain s' cap p bs ns stack :=
  h.frame hF (fun q _ => by simp [BlockCell, Field.array]) fun q hq => by
    simp only [NodeCell, Field.array, not_or]
    exact ⟨by omega, by omega, fun h => hdis q hq h.2⟩

/-- Exchange the headers in registers 68, 69 with those in 70, 71, through 72. -/
def swapProg : Cmd :=
  .seq (.assign 72 (.reg 68)) (.seq (.assign 68 (.reg 70)) (.seq (.assign 70 (.reg 72))
    (.seq (.assign 72 (.reg 69)) (.seq (.assign 69 (.reg 71)) (.assign 71 (.reg 72))))))

theorem swapProg_spec {w : ℕ} {s : State} (h68 : s.regs 68 < 2 ^ w) (h69 : s.regs 69 < 2 ^ w)
    (h70 : s.regs 70 < 2 ^ w) (h71 : s.regs 71 < 2 ^ w) :
    ∃ s', Exec w swapProg s s' 12 ∧ s'.arrs = s.arrs ∧ s'.regs 68 = s.regs 70 ∧
      s'.regs 69 = s.regs 71 ∧ s'.regs 70 = s.regs 68 ∧ s'.regs 71 = s.regs 69 ∧
      ∀ r, r ≠ 68 → r ≠ 69 → r ≠ 70 → r ≠ 71 → r ≠ 72 → s'.regs r = s.regs r := by
  refine ⟨_, Exec.seq (exec_mov h68) (Exec.seq (exec_mov (by simpa using h70))
    (Exec.seq (exec_mov (by simpa using h68)) (Exec.seq (exec_mov (by simpa using h69))
      (Exec.seq (exec_mov (by simpa using h71)) (exec_mov (by simpa using h69)))))),
    rfl, by simp, by simp, by simp, by simp, fun r h1 h2 h3 h4 h5 => by
      simp [h1, h2, h3, h4, h5]⟩

/-- One round of the old-block loop. -/
def oldBodyProg : Cmd :=
  .seq loadBlockProg
    (.seq (maxTagProg 73 70)
      (.seq (.ite (gtExpr 73) swapProg .skip)
        (.seq (maxTagProg 73 70)
          (.ite (gtExpr 73)
            (.seq (.assign 35 (.const 0)) (.assign 74 (.const 0)))
            (.seq (appendProg 65 66 68 69)
              (.seq (appendProg 63 64 70 71) (.seq popProg oldTestProg)))))))

/-- The old-block loop, with its first test. -/
def oldLoopProg : Cmd := .seq oldTestProg (.while (.reg 74) oldBodyProg)

/-- The state of the old-block loop: remaining stack, `L`, `R`, the addresses
of `L` and `R`, and the block and node addresses of the stack. `none` records
a rejection. -/
abbrev OldGhost :=
  Option (List Block × List ReturnNode × List ReturnNode × List ℕ × List ℕ × List ℕ × List ℕ)

/-- The invariant of the old-block loop. All node addresses involved form
the list `P₀` up to order. -/
def OldInv (D cap b : ℕ) (s₀ : State) (blocks₀ : List Block) (left₀ right₀ : List ReturnNode)
    (P₀ bs₀ : List ℕ) : OldGhost → State → Prop
  | none, s => Frame s₀ s (fun a q => a = Field.nodeNext.array ∧ q ∈ P₀) ∧ Words D s ∧
      s.regs 62 = b ∧ s.regs 35 = 0 ∧ s.regs 74 = 0 ∧ mergeOld b blocks₀ left₀ right₀ = none
  | some (rest, left, right, LA, RA, bs, ns), s =>
      Frame s₀ s (fun a q => a = Field.nodeNext.array ∧ q ∈ P₀) ∧ Words D s ∧
      s.regs 62 = b ∧ s.regs 35 = 1 ∧ BlockChain s cap (s.regs 67) bs ns rest ∧
      ListAt s cap (s.regs 65) (s.regs 66) LA left ∧
      ListAt s cap (s.regs 63) (s.regs 64) RA right ∧
      (LA ++ RA ++ ns).Perm P₀ ∧ bs <:+ bs₀ ∧ s.regs 74 = oldTestVal b rest ∧
      mergeOld b blocks₀ left₀ right₀ = mergeOld b rest left right

/-- One hundred twenty steps per remaining block. -/
def oldPot : OldGhost → ℕ
  | none => 0
  | some (rest, _, _, _, _, _, _) => 120 * (rest.length + 1)

private theorem perm_round {LA RA L R ns X Y P : List ℕ} (h : (LA ++ RA ++ (L ++ R ++ ns)).Perm P)
    (hXY : (X ++ Y).Perm (L ++ R)) : (LA ++ X ++ (RA ++ Y) ++ ns).Perm P := by
  refine List.Perm.trans ?_ h
  rw [List.perm_iff_count] at hXY ⊢
  intro a
  have := hXY a
  simp only [List.count_append] at this ⊢
  omega

theorem oldTestVal_lt (b : ℕ) (rest : List Block) : oldTestVal b rest ≤ 2 := by
  cases rest with
  | nil => simp [oldTestVal]
  | cons q r =>
    simp only [oldTestVal]
    split_ifs <;> omega

/-- One round of the old-block loop keeps its invariant and pays for itself. -/
theorem oldLoop_round {w D cap b : ℕ} {s₀ : State} {blocks₀ : List Block}
    {left₀ right₀ : List ReturnNode} {P₀ bs₀ : List ℕ} (hnd₀ : P₀.Nodup)
    (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 2 < 2 ^ w) (hb : b ≤ D) :
    ∀ g s, OldInv D cap b s₀ blocks₀ left₀ right₀ P₀ bs₀ g s →
      ∃ v, (Expr.reg 74).eval w s = some v ∧ (v ≠ 0 →
        ∃ g' s' t, Exec w oldBodyProg s s' t ∧
          OldInv D cap b s₀ blocks₀ left₀ right₀ P₀ bs₀ g' s' ∧
          (Expr.reg 74).cost + t + oldPot g' ≤ oldPot g) := by
  rintro (_ | ⟨rest, left, right, LA, RA, bs, ns⟩) s hI
  · obtain ⟨-, -, -, -, h74, -⟩ := hI
    exact ⟨0, by rw [eval_reg (by rw [h74]; exact Nat.pow_pos (by decide)), h74],
      fun h => absurd rfl h⟩
  obtain ⟨hF, hW, h62, h35, hB, hLA, hRA, hperm, hsuf, h74, heq⟩ := hI
  have h74w : s.regs 74 < 2 ^ w := by have := oldTestVal_lt b rest; omega
  refine ⟨_, eval_reg h74w, fun hv => ?_⟩
  cases rest with
  | nil => simp [h74, oldTestVal] at hv
  | cons blk rest' =>
  have hgt : blk.maximum > (b : Int) := (oldTestVal_cons_ne_zero b blk rest').mp (h74 ▸ hv)
  obtain ⟨q, hq⟩ : ∃ q, s.regs 67 = q := ⟨_, rfl⟩
  rw [hq] at hB
  cases hB with
  | @cons _ below lf ll rf rl bs' ns' L R _ _ hpos hqc hlf hll hrf hrl hbelow hL hR hrest =>
  rw [← hq] at hlf hll hrf hrl hbelow
  have hnd : (LA ++ RA ++ (L ++ R ++ ns')).Nodup := hperm.nodup_iff.mpr hnd₀
  have hqw : s.regs 67 < 2 ^ w := by omega
  obtain ⟨hlfc, hllc⟩ := hL.pointers_lt hcap
  obtain ⟨hrfc, hrlc⟩ := hR.pointers_lt hcap
  have hbelowD : below ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hbelow
  -- Load the block.
  let s₁ := (((s.setReg 68 lf).setReg 69 ll).setReg 70 rf).setReg 71 rl
  have hx₁ : Exec w loadBlockProg s s₁ 12 :=
    loadBlockProg_exec hqw hlf hll hrf hrl ⟨by omega, by omega, by omega, by omega⟩
  have hR₁ : ListAt s₁ cap (s₁.regs 70) (s₁.regs 71) R blk.right := by
    simpa [s₁] using hR.of_arrs_eq (s' := s₁) rfl
  obtain ⟨t₂, hx₂, ht₂⟩ := maxTagProg_spec (w := w) (D := D) (dst := 73) hR₁ hcap hcapD
    (by omega) hW
  let s₂ := s₁.setReg 73 (maxTag blk.right)
  have h62₂ : s₂.regs 62 = b := by simp [s₂, s₁, h62]
  have hg₂ := gtExpr_eval (w := w) (s := s₂) (r := 73) (by omega) (by rw [h62₂]; omega)
    (by simp [s₂]; have := hR.maxTag_le hW; omega)
  rw [h62₂, (show s₂.regs 73 = maxTag blk.right by simp [s₂])] at hg₂
  -- The block after the optional exchange of its sides.
  let q' : Block := if listMaximum blk.right > (b : Int) then ⟨blk.right, blk.left⟩ else blk
  obtain ⟨s₃, t₃, X, Y, hx₃, ht₃, harr₃, hX₃, hY₃, hXY, hregs₃⟩ : ∃ s₃ t₃ X Y,
      Exec w (.ite (gtExpr 73) swapProg .skip) s₂ s₃ t₃ ∧ t₃ ≤ 17 ∧ s₃.arrs = s.arrs ∧
      ListAt s₃ cap (s₃.regs 68) (s₃.regs 69) X q'.left ∧
      ListAt s₃ cap (s₃.regs 70) (s₃.regs 71) Y q'.right ∧ (X ++ Y).Perm (L ++ R) ∧
      ∀ r, r ≠ 68 → r ≠ 69 → r ≠ 70 → r ≠ 71 → r ≠ 72 → r ≠ 73 → s₃.regs r = s.regs r := by
    by_cases hsw : b + 1 < maxTag blk.right
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hsw)] at hg₂
      obtain ⟨s₃, hx, harr, h68, h69, h70, h71, hothers⟩ := swapProg_spec (w := w) (s := s₂)
        (by simp [s₂, s₁]; omega) (by simp [s₂, s₁]; omega) (by simp [s₂, s₁]; omega)
        (by simp [s₂, s₁]; omega)
      have hq'eq : q' = ⟨blk.right, blk.left⟩ := by
        simp [q', (listMaximum_gt_iff _ _).mpr hsw]
      refine ⟨s₃, _, R, L, exec_ite_eval hg₂ (fun _ => hx) (fun h => absurd h one_ne_zero),
        by simp [gtExpr], harr, ?_, ?_, List.perm_append_comm, fun r h1 h2 h3 h4 h5 h6 => ?_⟩
      · rw [hq'eq, h68, h69]
        simpa [s₂, s₁] using hR.of_arrs_eq (s' := s₃) harr
      · rw [hq'eq, h70, h71]
        simpa [s₂, s₁] using hL.of_arrs_eq (s' := s₃) harr
      · rw [hothers r h1 h2 h3 h4 h5]
        simp [s₂, s₁, h1, h2, h3, h4, h6]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hsw)] at hg₂
      have hq'eq : q' = blk := by
        simp [q', show ¬ listMaximum blk.right > (b : Int) from
          fun h => hsw ((listMaximum_gt_iff _ _).mp h)]
      refine ⟨s₂, _, L, R, exec_ite_eval hg₂ (fun h => absurd rfl h) (fun _ => Exec.skip s₂),
        by simp [gtExpr], rfl, ?_, ?_, List.Perm.refl _, fun r h1 h2 h3 h4 h5 h6 => ?_⟩
      · rw [hq'eq]
        simpa [s₂, s₁] using hL.of_arrs_eq (s' := s₂) rfl
      · rw [hq'eq]
        simpa [s₂, s₁] using hR.of_arrs_eq (s' := s₂) rfl
      · simp [s₂, s₁, h1, h2, h3, h4, h6]
  have hXYsub : ∀ a, a ∈ X ++ Y ↔ a ∈ L ++ R := fun a => hXY.mem_iff
  -- The right maximum of the selected block.
  have hW₃ : Words D s₃ := fun a h1 h2 y hy => hW a h1 h2 y (harr₃ ▸ hy)
  obtain ⟨t₄, hx₄, ht₄⟩ := maxTagProg_spec (w := w) (D := D) (dst := 73) hY₃ hcap hcapD
    (by omega) hW₃
  let s₄ := s₃.setReg 73 (maxTag q'.right)
  have h62₄ : s₄.regs 62 = b := by simp [s₄, hregs₃ 62 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h62]
  have hg₄ := gtExpr_eval (w := w) (s := s₄) (r := 73) (by omega) (by rw [h62₄]; omega)
    (by simp [s₄]; have := hY₃.maxTag_le hW₃; omega)
  rw [h62₄, (show s₄.regs 73 = maxTag q'.right by simp [s₄])] at hg₄
  have hmerge : mergeOld b (blk :: rest') left right = if listMaximum q'.right > (b : Int) then
      none else mergeOld b rest' (left ++ q'.left) (right ++ q'.right) := by
    rw [mergeOld, ite_eq_left_of_eq_true _ _ (eq_true hgt)]
  by_cases hrej : b + 1 < maxTag q'.right
  · -- Both sides of the selected block exceed `b`: reject.
    rw [ite_eq_left_of_eq_true _ _ (eq_true hrej)] at hg₄
    let s₅ := (s₄.setReg 35 0).setReg 74 0
    refine ⟨none, s₅, _, Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄
      (exec_ite_eval hg₄ (fun _ => Exec.seq (exec_setc (by omega)) (exec_setc (by omega)))
        (fun h => absurd h one_ne_zero))))), ⟨?_, ?_, ?_, by simp [s₅], by simp [s₅], ?_⟩, ?_⟩
    · exact hF.of_arrs_eq_right (by simp [s₅, s₄, harr₃])
    · exact fun a h1 h2 y hy => hW a h1 h2 y (by simpa [s₅, s₄, harr₃] using hy)
    · simp [s₅, h62₄]
    · rw [heq, hmerge, ite_eq_left_of_eq_true _ _ (eq_true ((listMaximum_gt_iff _ _).mpr hrej))]
    · simp only [oldPot, List.length_cons, Expr.cost_reg, gtExpr, Expr.cost_op, Expr.cost_const]
      omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hrej)] at hg₄
    -- Append the selected sides to `L` and `R`.
    have hD1 := List.disjoint_of_nodup_append hnd
    have hD2 := List.disjoint_of_nodup_append (List.nodup_append.mp hnd).1
    have hXm : ∀ a ∈ X, a ∈ L ++ R ++ ns' := fun a h =>
      List.mem_append_left _ ((hXYsub a).mp (List.mem_append_left _ h))
    have hYm : ∀ a ∈ Y, a ∈ L ++ R ++ ns' := fun a h =>
      List.mem_append_left _ ((hXYsub a).mp (List.mem_append_right _ h))
    have hdisLX : ∀ a ∈ LA, a ∉ X := fun a ha hx => hD1 (List.mem_append_left _ ha) (hXm a hx)
    have hdisLY : ∀ a ∈ LA, a ∉ Y := fun a ha hy => hD1 (List.mem_append_left _ ha) (hYm a hy)
    have hdisRY : ∀ a ∈ RA, a ∉ Y := fun a ha hy => hD1 (List.mem_append_right _ ha) (hYm a hy)
    have hdisLR : ∀ a ∈ LA, a ∉ RA := fun a ha hr => hD2 ha hr
    have hdisXR : ∀ a ∈ X, a ∉ RA := fun a hx hr => hD1 (List.mem_append_right _ hr) (hXm a hx)
    have hdisNL : ∀ a ∈ ns', a ∉ LA := fun a hn hl =>
      hD1 (List.mem_append_left _ hl) (List.mem_append_right _ hn)
    have hdisNR : ∀ a ∈ ns', a ∉ RA := fun a hn hr =>
      hD1 (List.mem_append_right _ hr) (List.mem_append_right _ hn)
    have hLA₄ : ListAt s₄ cap (s₄.regs 65) (s₄.regs 66) LA left := by
      simpa [s₄, hregs₃ 65 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hregs₃ 66 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] using
        hLA.of_arrs_eq (s' := s₄) (by simp [s₄, harr₃])
    have hX₄ : ListAt s₄ cap (s₄.regs 68) (s₄.regs 69) X q'.left := by
      simpa [s₄] using hX₃.of_arrs_eq (s' := s₄) rfl
    have hW₄ : Words D s₄ := hW₃
    obtain ⟨s₅, t₅, hx₅, ht₅, hL₅, hF₅, hregs₅, hW₅⟩ := appendProg_spec (w := w) (D := D)
      (fA := 65) (lA := 66) (fB := 68) (lB := 69) (by decide) (by decide) hLA₄ hX₄ hdisLX
      hcap hcapD (by omega) hW₄
    have hRA₅ : ListAt s₅ cap (s₅.regs 63) (s₅.regs 64) RA right := by
      rw [hregs₅ 63 (by decide) (by decide), hregs₅ 64 (by decide) (by decide)]
      refine ListAt.frame_next ?_ hF₅ (fun a ha hl => hdisLR a hl ha)
      simpa [s₄, hregs₃ 63 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hregs₃ 64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] using
        hRA.of_arrs_eq (s' := s₄) (by simp [s₄, harr₃])
    have hY₅ : ListAt s₅ cap (s₅.regs 70) (s₅.regs 71) Y q'.right := by
      rw [hregs₅ 70 (by decide) (by decide), hregs₅ 71 (by decide) (by decide)]
      exact ListAt.frame_next (by simpa [s₄] using hY₃.of_arrs_eq (s' := s₄) rfl) hF₅
        (fun a ha hl => hdisLY a hl ha)
    obtain ⟨s₆, t₆, hx₆, ht₆, hR₆, hF₆, hregs₆, hW₆⟩ := appendProg_spec (w := w) (D := D)
      (fA := 63) (lA := 64) (fB := 70) (lB := 71) (by decide) (by decide) hRA₅ hY₅ hdisRY
      hcap hcapD (by omega) hW₅
    have hL₆ : ListAt s₆ cap (s₆.regs 65) (s₆.regs 66) (LA ++ X) (left ++ q'.left) := by
      rw [hregs₆ 65 (by decide) (by decide), hregs₆ 66 (by decide) (by decide)]
      refine ListAt.frame_next hL₅ hF₆ (fun a ha hr => ?_)
      rcases List.mem_append.mp ha with ha | ha
      · exact hdisLR a ha hr
      · exact hdisXR a ha hr
    have h67₆ : s₆.regs 67 = q := by
      rw [hregs₆ 67 (by decide) (by decide), hregs₅ 67 (by decide) (by decide)]
      simp [s₄, hregs₃ 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hq]
    have harr₆ : ∀ a, a ≠ Field.nodeNext.array → s₆.arrs a = s.arrs a := by
      intro a ha
      have h1 := hF₆ a
      have h2 := hF₅ a
      apply List.ext_getElem?
      intro i
      rw [h1.2 i (by simp [ha]), h2.2 i (by simp [ha])]
      simp [s₄, harr₃]
    have hbelow₆ : (s₆.arrs Field.blockBelow.array)[s₆.regs 67]? = some below := by
      rw [h67₆, harr₆ _ (by simp [Field.array]), ← hq]
      exact hbelow
    let s₇ := s₆.setReg 67 below
    have hrest₇ : BlockChain s₇ cap (s₇.regs 67) bs' ns' rest' := by
      have h4 : BlockChain s₄ cap below bs' ns' rest' :=
        hrest.of_arrs_eq (by simp [s₄, harr₃])
      have h6 := (h4.frame_next hF₅ hdisNL).frame_next hF₆ hdisNR
      simpa [s₇] using h6.of_arrs_eq (s' := s₇) rfl
    have h62₇ : s₇.regs 62 = b := by
      simp [s₇, hregs₆ 62 (by decide) (by decide), hregs₅ 62 (by decide) (by decide), h62₄]
    obtain ⟨s₈, t₈, hx₈, ht₈, harr₈, h74₈, hregs₈⟩ := oldTestProg_spec (w := w) (D := D) hrest₇
      hW₆ (by rw [h62₇]; exact hb) hcap hcapD hD
    have hreg8 : ∀ r, r ≠ 68 → r ≠ 70 → r ≠ 72 → r ≠ 73 → r ≠ 74 → s₈.regs r = s₇.regs r := by
      intro r h1 h2 h3 h4 h5
      apply hregs₈
      simp [oldTestProg, maxTagProg, Cmd.writtenRegs, h1, h2, h3, h4, h5]
    refine ⟨some (rest', left ++ q'.left, right ++ q'.right, LA ++ X, RA ++ Y, bs', ns'), s₈, _,
      Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (exec_ite_eval hg₄
        (fun h => absurd rfl h) (fun _ => Exec.seq hx₅ (Exec.seq hx₆
          (Exec.seq (exec_ld (by rw [h67₆]; omega) hbelow₆ (by omega)) hx₈))))))),
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · refine (((hF.of_arrs_eq_right (s := s) (by simp [s₄, harr₃])).trans
        (hF₅.trans hF₆)).of_arrs_eq_right (by rw [harr₈]; rfl)).mono ?_
      intro a c hac
      have hPmem : ∀ x, x ∈ LA ++ RA ++ (L ++ R ++ ns') → x ∈ P₀ := fun x hx => hperm.mem_iff.mp hx
      rcases hac with h | h | h
      · exact h
      · exact ⟨h.1, hPmem c (by simp [h.2])⟩
      · exact ⟨h.1, hPmem c (by simp [h.2])⟩
    · exact fun a h1 h2 y hy => hW₆ a h1 h2 y (by simpa [s₇, harr₈] using hy)
    · rw [hreg8 62 (by decide) (by decide) (by decide) (by decide) (by decide), h62₇]
    · rw [hreg8 35 (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [s₇, hregs₆ 35 (by decide) (by decide), hregs₅ 35 (by decide) (by decide), s₄,
        hregs₃ 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h35]
    · rw [hreg8 67 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hrest₇.of_arrs_eq harr₈
    · rw [hreg8 65 (by decide) (by decide) (by decide) (by decide) (by decide),
        hreg8 66 (by decide) (by decide) (by decide) (by decide) (by decide)]
      simpa [s₇] using hL₆.of_arrs_eq (s' := s₈) (by rw [harr₈]; rfl)
    · rw [hreg8 63 (by decide) (by decide) (by decide) (by decide) (by decide),
        hreg8 64 (by decide) (by decide) (by decide) (by decide) (by decide)]
      simpa [s₇] using hR₆.of_arrs_eq (s' := s₈) (by rw [harr₈]; rfl)
    · exact perm_round hperm hXY
    · exact (List.suffix_cons q bs').trans hsuf
    · rw [h74₈, h62₇]
    · rw [heq, hmerge, ite_eq_right_of_eq_false _ _ (eq_false (fun h => hrej ((listMaximum_gt_iff _ _).mp h)))]
    · simp only [oldPot, List.length_cons, Expr.cost_reg, gtExpr, Expr.cost_op, Expr.cost_const]
      omega

/-- When the loop test fails, `mergeOld` returns its arguments. -/
theorem mergeOld_of_test_zero {b : ℕ} {rest : List Block} {left right : List ReturnNode}
    (h : oldTestVal b rest = 0) : mergeOld b rest left right = some (rest, left, right) := by
  cases rest with
  | nil => rfl
  | cons q rest =>
    have hq : ¬ q.maximum > (b : Int) := fun hq => (oldTestVal_cons_ne_zero b q rest).mpr hq h
    rw [mergeOld, ite_eq_right_of_eq_false _ _ (eq_false hq)]

/-- Part I, Section 4, the loop over the old stack in `MERGE`. Starting with 1
in register 35, `b` in register 62, the stack at register 67, and lists `L`
and `R` at registers 65, 66 and 63, 64, the loop refines `mergeOld b`. On a
rejection register 35 holds 0. Otherwise the remaining stack is a suffix of
the old one, and the node addresses of `L`, `R` and the stack are those at the
start up to order. Only next pointers of these nodes are written. The loop
costs at most 41 steps plus 120 per popped block. -/
theorem oldLoopProg_spec {w D cap : ℕ} {s : State} {blocks : List Block}
    {left right : List ReturnNode} {LA RA bs ns : List ℕ}
    (hB : BlockChain s cap (s.regs 67) bs ns blocks)
    (hL : ListAt s cap (s.regs 65) (s.regs 66) LA left)
    (hR : ListAt s cap (s.regs 63) (s.regs 64) RA right)
    (hnd : (LA ++ RA ++ ns).Nodup) (h35 : s.regs 35 = 1) (hW : Words D s)
    (hb : s.regs 62 ≤ D) (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 2 < 2 ^ w) :
    ∃ s' t, Exec w oldLoopProg s s' t ∧
      Frame s s' (fun a q => a = Field.nodeNext.array ∧ q ∈ LA ++ RA ++ ns) ∧ Words D s' ∧
      (∀ r, r ∉ oldLoopProg.writtenRegs → s'.regs r = s.regs r) ∧
      match mergeOld (s.regs 62) blocks left right with
      | none => s'.regs 35 = 0 ∧ t ≤ 120 * blocks.length + 161
      | some (blocks', left', right') => s'.regs 35 = 1 ∧ ∃ LA' RA' bs' ns',
          BlockChain s' cap (s'.regs 67) bs' ns' blocks' ∧ bs' <:+ bs ∧
          ListAt s' cap (s'.regs 65) (s'.regs 66) LA' left' ∧
          ListAt s' cap (s'.regs 63) (s'.regs 64) RA' right' ∧
          (LA' ++ RA' ++ ns').Perm (LA ++ RA ++ ns) ∧
          t + 120 * blocks'.length ≤ 120 * blocks.length + 41 := by
  set b := s.regs 62 with hbdef
  obtain ⟨s₀, t₀, hx₀, ht₀, harr₀, h74₀, hregs₀⟩ := oldTestProg_spec (w := w) (D := D) hB hW hb
    hcap hcapD hD
  have hreg0 : ∀ r, r ≠ 68 → r ≠ 70 → r ≠ 72 → r ≠ 73 → r ≠ 74 → s₀.regs r = s.regs r := by
    intro r h1 h2 h3 h4 h5
    apply hregs₀
    simp [oldTestProg, maxTagProg, Cmd.writtenRegs, h1, h2, h3, h4, h5]
  have hI₀ : OldInv D cap b s blocks left right (LA ++ RA ++ ns) bs
      (some (blocks, left, right, LA, RA, bs, ns)) s₀ := by
    refine ⟨Frame.of_arrs_eq harr₀ _, fun a h1 h2 y hy => hW a h1 h2 y (harr₀ ▸ hy), ?_, ?_, ?_,
      ?_, ?_, List.Perm.refl _, List.suffix_refl _, h74₀, rfl⟩
    · rw [hreg0 62 (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [hreg0 35 (by decide) (by decide) (by decide) (by decide) (by decide), h35]
    · rw [hreg0 67 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hB.of_arrs_eq harr₀
    · rw [hreg0 65 (by decide) (by decide) (by decide) (by decide) (by decide),
        hreg0 66 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hL.of_arrs_eq harr₀
    · rw [hreg0 63 (by decide) (by decide) (by decide) (by decide) (by decide),
        hreg0 64 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hR.of_arrs_eq harr₀
  obtain ⟨g, s', t, hx, hI, hstop, ht⟩ :=
    Exec.while_pot (OldInv D cap b s blocks left right (LA ++ RA ++ ns) bs) oldPot
      (oldLoop_round hnd hcap hcapD hD hb) _ s₀ hI₀
  have hx' : Exec w oldLoopProg s s' (t₀ + t) := Exec.seq hx₀ hx
  refine ⟨s', t₀ + t, hx', ?_, ?_, fun r hr => hx'.regs_eq_of_not_mem_writtenRegs hr, ?_⟩
  · rcases g with _ | ⟨rest, left', right', LA', RA', bs', ns'⟩
    · exact hI.1
    · exact hI.1
  · rcases g with _ | ⟨rest, left', right', LA', RA', bs', ns'⟩
    · exact hI.2.1
    · exact hI.2.1
  · rcases g with _ | ⟨rest, left', right', LA', RA', bs', ns'⟩
    · simp only [oldPot, Expr.cost_reg] at ht
      obtain ⟨-, -, -, h35', -, heq⟩ := hI
      rw [heq]
      exact ⟨h35', by omega⟩
    · simp only [oldPot, Expr.cost_reg] at ht
      obtain ⟨-, -, -, h35', hB', hL', hR', hperm, hsuf, h74, heq⟩ := hI
      have h74z : s'.regs 74 = 0 := by
        have hlt : s'.regs 74 < 2 ^ w := by have := oldTestVal_lt b rest; omega
        have := (eval_reg (s := s') (r := 74) hlt).symm.trans hstop
        simpa using this
      rw [heq, mergeOld_of_test_zero (h74 ▸ h74z)]
      exact ⟨h35', LA', RA', bs', ns', hB', hsuf, hL', hR', hperm, by omega⟩

end GraphMinor.Compute.PlanarityRam
