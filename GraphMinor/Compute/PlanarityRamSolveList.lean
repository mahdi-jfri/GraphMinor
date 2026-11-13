module

public import GraphMinor.Compute.PlanarityRamSolveFrame
import GraphMinor.Compute.WhileRounds

/-!
# List operations of the solver on the Word RAM

Part I, Section 3 of the planarity note stores a list of returns as a chain
of nodes with a first and a last pointer. This file gives the RAM programs
for the list operations that `MERGE` and `TRIM` use, and proves that each one
refines its Lean function:

* `appendProg`: destructive concatenation, by at most one pointer write
  (`appendProg_spec`), in at most 7 steps;
* `maxTagProg`: the first depth plus one, or zero for the empty list, which
  is `listMaximum + 1` (`maxTagProg_spec`);
* `lastDepthProg`: the last depth, which is `listMinimum` (`lastDepthProg_spec`);
* `trimListProg`: removal of the first nodes of a given depth
  (`trimListProg_spec`), in time linear in the number of removed nodes.

The headers of the lists live in registers. The programs read only words of
the node arrays, so they need the words there to fit the word size; `Words D s`
bounds them by `D`.

The file starts with small evaluation lemmas for the commands these programs
use.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-! ### Evaluating simple expressions and commands -/

theorem eval_reg {w : ℕ} {s : State} {r : ℕ} (h : s.regs r < 2 ^ w) :
    (Expr.reg r).eval w s = some (s.regs r) := by
  simp [Expr.eval, checkWord_of_lt h]

theorem eval_const {w n : ℕ} {s : State} (h : n < 2 ^ w) :
    (Expr.const n).eval w s = some n := by
  simp [Expr.eval, checkWord_of_lt h]

theorem eval_read {w : ℕ} {s : State} {a i v : ℕ} {idx : Expr} (hi : idx.eval w s = some i)
    (hv : (s.arrs a)[i]? = some v) (hvw : v < 2 ^ w) :
    (Expr.read a idx).eval w s = some v := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hv
  simp [Expr.eval, hi, hlt, heq, checkWord_of_lt hvw]

theorem eval_op {w : ℕ} {s : State} {bop : BinOp} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (Expr.op bop e₁ e₂).eval w s = bop.eval w v₁ v₂ := by
  simp [Expr.eval, h₁, h₂]

theorem binop_add {w a b : ℕ} (h : a + b < 2 ^ w) :
    BinOp.eval w .add a b = some (a + b) := by
  simp [BinOp.eval, BinOp.raw, checkWord_of_lt h]

theorem binop_eq {w a b : ℕ} (hw : 1 < 2 ^ w) :
    BinOp.eval w .eq a b = some (if a = b then 1 else 0) := by
  simp only [BinOp.eval, BinOp.raw]
  split <;> simp [checkWord_of_lt hw, checkWord_of_lt (by omega : 0 < 2 ^ w)]

theorem binop_lt {w a b : ℕ} (hw : 1 < 2 ^ w) :
    BinOp.eval w .lt a b = some (if a < b then 1 else 0) := by
  simp only [BinOp.eval, BinOp.raw]
  split <;> simp [checkWord_of_lt hw, checkWord_of_lt (by omega : 0 < 2 ^ w)]

theorem exec_mov {w : ℕ} {s : State} {dst src : ℕ} (h : s.regs src < 2 ^ w) :
    Exec w (.assign dst (.reg src)) s (s.setReg dst (s.regs src)) 2 :=
  Exec.assign (eval_reg h)

theorem exec_setc {w : ℕ} {s : State} {dst n : ℕ} (h : n < 2 ^ w) :
    Exec w (.assign dst (.const n)) s (s.setReg dst n) 2 :=
  Exec.assign (eval_const h)

theorem exec_ld {w : ℕ} {s : State} {dst a src v : ℕ} (hs : s.regs src < 2 ^ w)
    (hv : (s.arrs a)[s.regs src]? = some v) (hvw : v < 2 ^ w) :
    Exec w (.assign dst (.read a (.reg src))) s (s.setReg dst v) 3 :=
  Exec.assign (eval_read (eval_reg hs) hv hvw)

theorem exec_st {w : ℕ} {s : State} {a idx val : ℕ} (hi : s.regs idx < (s.arrs a).length)
    (hiw : s.regs idx < 2 ^ w) (hv : s.regs val < 2 ^ w) :
    Exec w (.write a (.reg idx) (.reg val)) s (s.writeArr a (s.regs idx) (s.regs val)) 3 :=
  Exec.write (eval_reg hiw) (eval_reg hv) hi

theorem exec_ite_pos {w : ℕ} {s s' : State} {r t : ℕ} {c₁ c₂ : Cmd} (hr : s.regs r ≠ 0)
    (hw : s.regs r < 2 ^ w) (h : Exec w c₁ s s' t) :
    Exec w (.ite (.reg r) c₁ c₂) s s' (1 + t) := by
  simpa using Exec.ite_true (c₂ := c₂) (eval_reg hw) hr h

theorem exec_ite_zero {w : ℕ} {s s' : State} {r t : ℕ} {c₁ c₂ : Cmd} (hr : s.regs r = 0)
    (h : Exec w c₂ s s' t) : Exec w (.ite (.reg r) c₁ c₂) s s' (1 + t) := by
  have h0 : (Expr.reg r).eval w s = some 0 := by
    rw [eval_reg (by rw [hr]; exact Nat.pow_pos (by decide))]
    simp [hr]
  simpa using Exec.ite_false (c₁ := c₁) h0 h

/-- The words of the solver arrays (arrays 50 to 62) are at most `D`. -/
def Words (D : ℕ) (s : State) : Prop :=
  ∀ a, 50 ≤ a → a ≤ 62 → ∀ x ∈ s.arrs a, x ≤ D

theorem Words.setReg {D : ℕ} {s : State} (h : Words D s) (r v : ℕ) : Words D (s.setReg r v) :=
  h

theorem Words.writeArr {D : ℕ} {s : State} (h : Words D s) (a i : ℕ) {v : ℕ} (hv : v ≤ D) :
    Words D (s.writeArr a i v) := by
  intro a' h1 h2 x hx
  by_cases ha : a' = a
  · subst ha
    simp only [State.writeArr_arrs_self] at hx
    rcases List.mem_or_eq_of_mem_set hx with hx | hx
    · exact h a' h1 h2 x hx
    · exact hx ▸ hv
  · simp only [State.writeArr_arrs_ne _ _ _ ha] at hx
    exact h a' h1 h2 x hx

theorem Words.get {D : ℕ} {s : State} (h : Words D s) {a i v : ℕ} (h1 : 50 ≤ a) (h2 : a ≤ 62)
    (hv : (s.arrs a)[i]? = some v) : v ≤ D :=
  h a h1 h2 v (List.mem_of_getElem? hv)

/-! ### Lists -/

/-- A list depends only on the arrays of the state. -/
theorem ListAt.of_arrs_eq {s s' : State} {cap f l : ℕ} {A : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x) (he : s'.arrs = s.arrs) : ListAt s' cap f l A x :=
  h.frame (Frame.of_arrs_eq he (fun _ _ => False)) (fun _ _ => by simp [NodeCell])

/-- Both pointers of a list header are below the capacity. -/
theorem ListAt.pointers_lt {s : State} {cap f l : ℕ} {A : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x) (hcap : 0 < cap) : f < cap ∧ l < cap := by
  refine ⟨h.1.first_lt hcap, ?_⟩
  rw [h.2.1]
  cases hA : A.getLast? with
  | none => exact hcap
  | some q => exact (h.1.mem_bounds q (List.mem_of_getLast? hA)).2

/-- Every address of a chain is a valid index of the next array. -/
theorem NodeChain.next_lt_length {s : State} {cap f : ℕ} {A : List ℕ} {x : List ReturnNode}
    (hc : NodeChain s cap f A x) : ∀ q ∈ A, q < (s.arrs Field.nodeNext.array).length := by
  induction hc with
  | nil => simp
  | @cons p q ps b bs _ _ _ _ hn _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (List.getElem?_eq_some_iff.mp hn).1
    · exact ih r hr

/-- The last pointer of a nonempty list is a valid index of the next array. -/
theorem ListAt.last_lt_length {s : State} {cap f l : ℕ} {A : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x) (hA : A ≠ []) :
    l < (s.arrs Field.nodeNext.array).length := by
  have hl : l = A.getLast hA := by
    rw [h.2.1, List.getLast?_eq_some_getLast hA]
    rfl
  exact h.1.next_lt_length l (hl ▸ List.getLast_mem hA)

/-- `appendProg fA lA fB lB` appends the list with header `(fB, lB)` to the
list with header `(fA, lA)`, as in `_List.append` of `docs/planarity/planarity_linear.py`. -/
def appendProg (fA lA fB lB : ℕ) : Cmd :=
  .ite (.reg fB)
    (.seq (.ite (.reg fA) (.write Field.nodeNext.array (.reg lA) (.reg fB))
        (.assign fA (.reg fB)))
      (.assign lA (.reg lB)))
    .skip

/-- Part I, Section 3, concatenation, on the RAM: at most 7 steps, one write
to the next pointer of the old last node, and the header registers hold the
header of the concatenation. -/
theorem appendProg_spec {w D cap : ℕ} {s : State} {fA lA fB lB : ℕ}
    (h1 : fA ≠ lA) (h3 : fA ≠ lB)
    {A B : List ℕ} {x y : List ReturnNode}
    (hA : ListAt s cap (s.regs fA) (s.regs lA) A x) (hB : ListAt s cap (s.regs fB) (s.regs lB) B y)
    (hdis : ∀ q ∈ A, q ∉ B) (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w)
    (hW : Words D s) :
    ∃ s' t, Exec w (appendProg fA lA fB lB) s s' t ∧ t ≤ 7 ∧
      ListAt s' cap (s'.regs fA) (s'.regs lA) (A ++ B) (x ++ y) ∧
      Frame s s' (fun a q => a = Field.nodeNext.array ∧ q ∈ A) ∧
      (∀ r, r ≠ fA → r ≠ lA → s'.regs r = s.regs r) ∧ Words D s' := by
  have hpA := hA.pointers_lt hcap
  have hpB := hB.pointers_lt hcap
  have hwA : s.regs fA < 2 ^ w := by omega
  have hwlA : s.regs lA < 2 ^ w := by omega
  have hwB : s.regs fB < 2 ^ w := by omega
  have hwlB : s.regs lB < 2 ^ w := by omega
  -- The result is the representation lemma `ListAt.append` in all three cases.
  have key : ∀ s' : State,
      Frame s s' (fun a q => a = Field.nodeNext.array ∧ q = s.regs lA ∧
        s.regs fA ≠ 0 ∧ s.regs fB ≠ 0) →
      (s.regs fA ≠ 0 → s.regs fB ≠ 0 →
        (s'.arrs Field.nodeNext.array)[s.regs lA]? = some (s.regs fB)) →
      s'.regs fA = appendFirst (s.regs fA) (s.regs fB) →
      s'.regs lA = appendLast (s.regs lA) (s.regs fB) (s.regs lB) →
      ListAt s' cap (s'.regs fA) (s'.regs lA) (A ++ B) (x ++ y) ∧
        Frame s s' (fun a q => a = Field.nodeNext.array ∧ q ∈ A) := by
    intro s' hF hlast hf hl
    rw [hf, hl]
    refine ⟨hA.append hB hdis hF hlast, hF.mono ?_⟩
    rintro a q ⟨ha, hq, hfA, _⟩
    refine ⟨ha, ?_⟩
    have hAne : A ≠ [] := fun h => hfA (hA.first_eq_zero_iff.mpr h)
    rw [hq, hA.2.1, List.getLast?_eq_some_getLast hAne]
    exact List.getLast_mem hAne
  by_cases hfB : s.regs fB = 0
  · have hk := key s (Frame.refl s _) (fun _ h => absurd hfB h)
      (by simp [appendFirst, hfB]) (by simp [appendLast, hfB])
    exact ⟨s, _, exec_ite_zero hfB (Exec.skip s), by omega, hk.1, hk.2, fun _ _ _ => rfl, hW⟩
  · by_cases hfA : s.regs fA = 0
    · let s₁ := s.setReg fA (s.regs fB)
      let s₂ := s₁.setReg lA (s.regs lB)
      have hx : Exec w (appendProg fA lA fB lB) s s₂ (1 + (1 + 2 + 2)) :=
        exec_ite_pos hfB hwB (Exec.seq (exec_ite_zero hfA (exec_mov hwB))
          (by simpa [s₁, h3.symm] using
            (exec_mov (s := s₁) (dst := lA) (src := lB) (by simpa [s₁, h3.symm] using hwlB))))
      have hk := key s₂ (Frame.of_arrs_eq rfl _) (fun h => absurd hfA h)
        (by simp [s₂, s₁, h1, appendFirst, hfA, hfB])
        (by simp [s₂, s₁, appendLast, hfB])
      refine ⟨s₂, _, hx, by omega, hk.1, hk.2, ?_, (hW.setReg _ _).setReg _ _⟩
      intro r hr1 hr2
      simp [s₂, s₁, hr1, hr2]
    · let s₁ := s.writeArr Field.nodeNext.array (s.regs lA) (s.regs fB)
      let s₂ := s₁.setReg lA (s.regs lB)
      have hAne : A ≠ [] := fun h => hfA (hA.first_eq_zero_iff.mpr h)
      have hlen := hA.last_lt_length hAne
      have hx : Exec w (appendProg fA lA fB lB) s s₂ (1 + (1 + 3 + 2)) :=
        exec_ite_pos hfB hwB (Exec.seq (exec_ite_pos hfA hwA (exec_st hlen hwlA hwB))
          (exec_mov (s := s₁) (dst := lA) (src := lB) hwlB))
      have hF : Frame s s₂ (fun a q => a = Field.nodeNext.array ∧ q = s.regs lA ∧
          s.regs fA ≠ 0 ∧ s.regs fB ≠ 0) :=
        ((Frame.writeArr s _ _ _).trans (Frame.setReg s₁ lA (s.regs lB) (fun _ _ => False))).mono
          (fun a q h => by rcases h with h | h <;> simp_all)
      have hk := key s₂ hF (fun _ _ => by simp [s₂, s₁, hlen])
        (by simp [s₂, s₁, h1, appendFirst, hfA, hfB])
        (by simp [s₂, s₁, appendLast, hfB])
      refine ⟨s₂, _, hx, by omega, hk.1, hk.2, ?_, ?_⟩
      · intro r hr1 hr2
        simp [s₂, s₁, hr2]
      · exact (hW.writeArr _ _ (by omega)).setReg _ _

/-- The first depth plus one, or zero for the empty list. -/
def maxTag : List ReturnNode → ℕ
  | [] => 0
  | b :: _ => b.depth + 1

theorem maxTag_eq (x : List ReturnNode) : (maxTag x : Int) = listMaximum x + 1 := by
  cases x <;> simp [maxTag, listMaximum]

/-- `listMaximum x > b` in terms of the tag. -/
theorem listMaximum_gt_iff (x : List ReturnNode) (b : ℕ) :
    listMaximum x > (b : Int) ↔ b + 1 < maxTag x := by
  have := maxTag_eq x
  omega

/-- `dst := maxTag` of the list whose first pointer is in `src`. -/
def maxTagProg (dst src : ℕ) : Cmd :=
  .ite (.reg src)
    (.assign dst (.op .add (.read Field.nodeDepth.array (.reg src)) (.const 1)))
    (.assign dst (.const 0))

/-- `maxTagProg` computes `maxTag` in at most 7 steps and changes only `dst`. -/
theorem maxTagProg_spec {w D cap : ℕ} {s : State} {dst src l : ℕ} {A : List ℕ}
    {x : List ReturnNode} (hA : ListAt s cap (s.regs src) l A x) (hcap : 0 < cap)
    (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) (hW : Words D s) :
    ∃ t, Exec w (maxTagProg dst src) s (s.setReg dst (maxTag x)) t ∧ t ≤ 7 := by
  have hp := hA.pointers_lt hcap
  have hws : s.regs src < 2 ^ w := by omega
  cases x with
  | nil =>
    have h0 : s.regs src = 0 := hA.1.first_eq_zero_iff.mpr rfl
    exact ⟨_, exec_ite_zero h0 (exec_setc (by omega)), by omega⟩
  | cons b x =>
    have hne : s.regs src ≠ 0 := fun h => by simpa using hA.1.first_eq_zero_iff.mp h
    have hd := hA.first_depth
    have hdD : b.depth ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hd
    refine ⟨_, exec_ite_pos hne hws (Exec.assign (eval_op (eval_read (eval_reg hws) hd
      (by omega)) (eval_const (by omega)) |>.trans (binop_add (by omega)))), ?_⟩
    simp

/-- `dst := listMinimum` of the list whose last pointer is in `src`. -/
def lastDepthProg (dst src : ℕ) : Cmd :=
  .ite (.reg src) (.assign dst (.read Field.nodeDepth.array (.reg src))) (.assign dst (.const 0))

/-- `lastDepthProg` computes `listMinimum` in at most 4 steps and changes only `dst`. -/
theorem lastDepthProg_spec {w D cap : ℕ} {s : State} {dst src f : ℕ} {A : List ℕ}
    {x : List ReturnNode} (hA : ListAt s cap f (s.regs src) A x) (hcap : 0 < cap)
    (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) (hW : Words D s) :
    ∃ t, Exec w (lastDepthProg dst src) s (s.setReg dst (listMinimum x)) t ∧ t ≤ 4 := by
  have hp := hA.pointers_lt hcap
  have hws : s.regs src < 2 ^ w := by omega
  by_cases hx : x = []
  · subst hx
    have hA0 : A = [] := by
      have := hA.1.length_eq
      exact List.length_eq_zero_iff.mp (by simpa using this)
    have h0 : s.regs src = 0 := hA.last_eq_zero_iff.mpr hA0
    have hmin : listMinimum ([] : List ReturnNode) = 0 := rfl
    rw [hmin]
    exact ⟨1 + 2, exec_ite_zero h0 (exec_setc (by omega)), by omega⟩
  · have hA0 : A ≠ [] := fun h => hx (by
      have := hA.1.length_eq
      rw [h] at this
      exact List.length_eq_zero_iff.mp this.symm)
    have hne : s.regs src ≠ 0 := fun h => hA0 (hA.last_eq_zero_iff.mp h)
    have hd := hA.last_depth hx
    have hdD := hW.get (by simp [Field.array]) (by simp [Field.array]) hd
    have hmin : listMinimum x = (x.getLast hx).depth := by
      simp [listMinimum, List.getLast?_eq_some_getLast hx]
    rw [hmin]
    exact ⟨_, exec_ite_pos hne hws (exec_ld hws hd (by omega)), le_refl _⟩

/-- One for a list whose first depth is `c`, and zero otherwise. -/
def trimTest (x : List ReturnNode) (c : ℕ) : ℕ :=
  match x with
  | [] => 0
  | b :: _ => if b.depth = c then 1 else 0

/-- `cont := trimTest` of the list whose first pointer is in `f`. -/
def trimTestProg (f c cont : ℕ) : Cmd :=
  .ite (.reg f) (.assign cont (.op .eq (.read Field.nodeDepth.array (.reg f)) (.reg c)))
    (.assign cont (.const 0))

theorem trimTestProg_spec {w D cap : ℕ} {s : State} {f c cont : ℕ} {A : List ℕ}
    {x : List ReturnNode} (hA : NodeChain s cap (s.regs f) A x) (hcap : 0 < cap)
    (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) (hW : Words D s) (hc : s.regs c ≤ D) :
    ∃ t, Exec w (trimTestProg f c cont) s (s.setReg cont (trimTest x (s.regs c))) t ∧
      t ≤ 6 := by
  have hp := hA.first_lt hcap
  have hws : s.regs f < 2 ^ w := by omega
  obtain ⟨fv, hfv⟩ : ∃ fv, s.regs f = fv := ⟨_, rfl⟩
  rw [hfv] at hA
  cases hA with
  | nil =>
    exact ⟨1 + 2, exec_ite_zero hfv (exec_setc (by omega)), by omega⟩
  | @cons p q ps b bs hpos _ _ hd _ _ =>
    rw [← hfv] at hd
    have hne : s.regs f ≠ 0 := by omega
    have hdD : b.depth ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hd
    have he := eval_op (bop := .eq) (eval_read (eval_reg hws) hd (by omega))
      (eval_reg (s := s) (r := c) (by omega))
    rw [binop_eq (by omega)] at he
    exact ⟨_, exec_ite_pos hne hws (Exec.assign he), by simp⟩

/-- `trimListProg f l c cont` removes the first nodes of depth `c` from the
list with header `(f, l)`, as in `_List.trim` of `docs/planarity/planarity_linear.py`. -/
def trimListProg (f l c cont : ℕ) : Cmd :=
  .seq (trimTestProg f c cont)
    (.seq (.while (.reg cont)
        (.seq (.assign f (.read Field.nodeNext.array (.reg f))) (trimTestProg f c cont)))
      (.ite (.reg f) .skip (.assign l (.const 0))))

/-- The predicate of `trimBlocks`. -/
abbrev depthIs (c : ℕ) : ReturnNode → Bool := fun b => b.depth == c

private theorem getLast?_of_suffix {A A' : List ℕ} (h : A' <:+ A) (hne : A' ≠ []) :
    A'.getLast? = A.getLast? := by
  obtain ⟨B, rfl⟩ := h
  rw [List.getLast?_append, List.getLast?_eq_some_getLast hne]
  rfl

/-- Part I, Section 5, "remove all first nodes of Q.L whose depth is c ... update
the last pointer of an emptied list to null": the program reads only the node
arrays and spends at most 10 steps plus 10 per removed node. -/
theorem trimListProg_spec {w D cap : ℕ} {s : State} {f l c cont : ℕ}
    (hfl : f ≠ l) (hfc : f ≠ c) (hfk : f ≠ cont) (hlk : l ≠ cont) (hck : c ≠ cont)
    {A : List ℕ} {x : List ReturnNode} (hA : ListAt s cap (s.regs f) (s.regs l) A x)
    (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) (hW : Words D s)
    (hc : s.regs c ≤ D) :
    ∃ s' t A', Exec w (trimListProg f l c cont) s s' t ∧
      t ≤ 10 + 10 * (x.length - (x.dropWhile (depthIs (s.regs c))).length) ∧
      s'.arrs = s.arrs ∧ A' <:+ A ∧
      ListAt s' cap (s'.regs f) (s'.regs l) A' (x.dropWhile (depthIs (s.regs c))) ∧
      (∀ r, r ≠ f → r ≠ l → r ≠ cont → s'.regs r = s.regs r) := by
  set cv := s.regs c with hcv
  -- The loop keeps a chain from the current first pointer, a suffix of the
  -- addresses, and the result of the test for the current first node.
  let I : (List ℕ × List ReturnNode) → State → Prop := fun g s' =>
    s'.arrs = s.arrs ∧ NodeChain s' cap (s'.regs f) g.1 g.2 ∧ g.1 <:+ A ∧
      x.dropWhile (depthIs cv) = g.2.dropWhile (depthIs cv) ∧
      s'.regs cont = trimTest g.2 cv ∧ g.2.length ≤ x.length ∧
      (∀ r, r ≠ f → r ≠ cont → s'.regs r = s.regs r)
  have hround : ∀ g s', I g s' → ∃ v, (Expr.reg cont).eval w s' = some v ∧ (v ≠ 0 →
      ∃ g' s'' t, Exec w (.seq (.assign f (.read Field.nodeNext.array (.reg f)))
        (trimTestProg f c cont)) s' s'' t ∧ I g' s'' ∧
        (Expr.reg cont).cost + t + 10 * g'.2.length ≤ 10 * g.2.length) := by
    rintro ⟨A', x'⟩ s' ⟨harr, hch, hsuf, hdrop, hk, hlen, hregs⟩
    have hkw : s'.regs cont < 2 ^ w := by
      rw [hk]; unfold trimTest; split <;> [omega; split <;> omega]
    refine ⟨_, eval_reg hkw, fun hv => ?_⟩
    obtain ⟨fv, hfv⟩ : ∃ fv, s'.regs f = fv := ⟨_, rfl⟩
    rw [hfv] at hch
    cases hch with
    | nil => simp [hk, trimTest] at hv
    | @cons p q ps b bs hpos hpc _ hd hn hrest =>
      rw [← hfv] at hd hn
      have hbc : b.depth = cv := by
        by_contra hne
        simp [hk, trimTest, hne] at hv
      have hpw : s'.regs f < 2 ^ w := by omega
      have hW' : Words D s' := fun a h1 h2 y hy => hW a h1 h2 y (harr ▸ hy)
      have hqD : q ≤ D := hW'.get (by simp [Field.array]) (by simp [Field.array]) hn
      let s₁ := s'.setReg f q
      have hc₁ : s₁.regs c = cv := by
        simp only [s₁, State.setReg_regs, hfc.symm, ↓reduceIte]
        rw [hregs c hfc.symm hck]
      have hch₁ : NodeChain s₁ cap (s₁.regs f) ps bs := by
        simpa [s₁] using hrest.frame (Frame.setReg s' f q (fun _ _ => False))
          (fun _ _ => by simp [NodeCell])
      obtain ⟨t₂, hx₂, ht₂⟩ := trimTestProg_spec (cont := cont) hch₁ hcap hcapD hD
        (hW'.setReg f q) (by rw [hc₁]; omega)
      refine ⟨(ps, bs), _, _, Exec.seq (exec_ld hpw hn (by omega)) hx₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simpa [s₁] using harr
      · rw [State.setReg_regs_ne _ _ hfk]
        exact hch₁.frame (Frame.setReg s₁ cont _ (fun _ _ => False)) (fun _ _ => by simp [NodeCell])
      · exact (List.suffix_cons _ _).trans hsuf
      · rw [hdrop, List.dropWhile_cons_of_pos (by simp [depthIs, hbc])]
      · simp [hc₁]
      · dsimp only at hlen ⊢
        simp only [List.length_cons] at hlen
        omega
      · intro r hr1 hr2
        simp [s₁, State.setReg_regs, hr1, hr2, hregs r hr1 hr2]
      · simp; omega
  -- The first test.
  have hp := hA.pointers_lt hcap
  obtain ⟨t₀, hx₀, ht₀⟩ := trimTestProg_spec (cont := cont) hA.1 hcap hcapD hD hW (by omega)
  let s₀ := s.setReg cont (trimTest x cv)
  have hI₀ : I (A, x) s₀ := by
    refine ⟨rfl, ?_, List.suffix_refl A, rfl, by simp [s₀], le_refl _, ?_⟩
    · simpa [s₀, State.setReg_regs, hfk] using hA.1.frame (Frame.setReg s cont _ (fun _ _ => False))
        (fun _ _ => by simp [NodeCell])
    · intro r _ hr2
      simp [s₀, hr2]
  obtain ⟨⟨A', x'⟩, s₁, t₁, hx₁, ⟨harr, hch, hsuf, hdrop, hk, hlen, hregs⟩, hstop, ht₁⟩ :=
    Exec.while_pot I (fun g => 10 * g.2.length) hround (A, x) s₀ hI₀
  dsimp only at harr hch hsuf hdrop hk hlen hregs ht₁
  -- When the loop stops, no first node has depth `c`.
  have hk0 : s₁.regs cont = 0 := by
    have := (eval_reg (w := w) (s := s₁) (r := cont) (by
      rw [hk]; unfold trimTest; split <;> [omega; split <;> omega])).symm.trans hstop
    simpa using this
  have hx' : x.dropWhile (depthIs cv) = x' := by
    rw [hdrop]
    cases x' with
    | nil => rfl
    | cons b x'' =>
      have hbc : b.depth ≠ cv := by
        intro hbc
        simp [hk, trimTest, hbc] at hk0
      rw [List.dropWhile_cons_of_neg (by simp [depthIs, hbc])]
  have hlen' : (x.dropWhile (depthIs cv)).length = x'.length := by rw [hx']
  have hp₁ := hch.first_lt hcap
  have hw₁ : s₁.regs f < 2 ^ w := by omega
  have hl₁ : s₁.regs l = s.regs l := by
    rw [hregs l hfl.symm hlk]
  have hnd' : A'.Nodup := hA.2.2.sublist hsuf.sublist
  by_cases hf0 : s₁.regs f = 0
  · have hA' : A' = [] := by
      have h1 := hch.first_eq_zero_iff.mp hf0
      have h2 := hch.length_eq
      rw [h1] at h2
      exact List.length_eq_zero_iff.mp h2
    let s₂ := s₁.setReg l 0
    refine ⟨s₂, _, A', Exec.seq hx₀ (Exec.seq hx₁ (exec_ite_zero hf0 (exec_setc (by omega)))),
      ?_, by simpa [s₂] using harr, hsuf, ?_, ?_⟩
    · simp only [Expr.cost_reg] at ht₁
      rw [hlen']
      omega
    · rw [hx']
      refine ⟨by simpa [s₂, State.setReg_regs, hfl] using hch.frame (Frame.setReg s₁ l 0
        (fun _ _ => False)) (fun _ _ => by simp [NodeCell]), by simp [s₂, hA'], hnd'⟩
    · intro r hr1 hr2 hr3
      simp [s₂, hr2, hregs r hr1 hr3]
  · have hA' : A' ≠ [] := fun h => hf0 (hch.first_eq_zero_iff.mpr (by
      have := hch.length_eq
      rw [h] at this
      exact List.length_eq_zero_iff.mp this.symm))
    refine ⟨s₁, _, A', Exec.seq hx₀ (Exec.seq hx₁ (exec_ite_pos hf0 hw₁ (Exec.skip s₁))),
      ?_, harr, hsuf, ?_, ?_⟩
    · simp only [Expr.cost_reg] at ht₁
      rw [hlen']
      omega
    · rw [hx', hl₁, hA.2.1, ← getLast?_of_suffix hsuf hA']
      exact ⟨hch, rfl, hnd'⟩
    · intro r hr1 hr2 hr3
      simp [hregs r hr1 hr3]

end GraphMinor.Compute.PlanarityRam
