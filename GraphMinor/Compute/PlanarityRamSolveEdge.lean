module

public import GraphMinor.Compute.PlanarityRamSolvePool
public import GraphMinor.Compute.PlanarityRamSolveFacts
public import GraphMinor.Compute.PlanarityRamSolveClaim
public import GraphMinor.Compute.PlanarityRamBounds

/-!
# One outgoing edge on the Word RAM

Part I, Section 6 of the planarity note integrates the outgoing edges of a
vertex one at a time:

    for each outgoing edge e of v, in key order:
        if e is a tree edge: C := the stored summary of its head
        else: C := the singleton summary of the back edge
        S := MERGE(S, C)

This file sets up the state of the solver loop and builds the child `C`:
`leafChildProg_spec` for a back edge and `treeChildMoveProg_spec` for a tree
edge. The round itself is `edgeRound` in `PlanarityRamSolveRound.lean`.

The state has three parts. The arrays below 50 hold the search data and the
outgoing lists, and never change. The pool (`PoolAt`) holds the summaries:
slot `v < N` the stored summary of vertex `v`, slot `N` the current summary
`S`, and slot `N + 1` the child summary `C` during a round. The result array
holds the record pointers of the slots `v < N`.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-! ### The input and the parts of the state that never change -/

/-- The hypotheses of `PlanarityRamSolveClaim` used by the loop proofs, with
`K = 4`. -/
structure SolveInput (N M w : ℕ) (search : Search) (s₀ : State) : Prop where
  word : 4 * (N + M + 1) < 2 ^ w
  searchAt : SearchAt N M s₀ search
  bounded : SearchBounded N search
  outgoing : OutgoingAt N s₀ (bucketOrder N search.edges)

/-- The arrays below 50 and the registers below 52 other than 35 keep their
values, the solver words are at most `N + M + 1`, and the arenas keep their
lengths. -/
def Common (N M : ℕ) (s₀ s : State) : Prop :=
  (∀ a : ℕ, a < 50 → s.arrs a = s₀.arrs a) ∧
  (∀ r : ℕ, r < 35 ∨ (35 < r ∧ r < 52) → s.regs r = s₀.regs r) ∧
  Words (N + M + 1) s ∧ SolverArenasAt N M s

theorem Frame.arr_eq {s s' : State} {W : ℕ → ℕ → Prop} (hF : Frame s s' W) {a : ℕ}
    (ha : ∀ q, ¬ W a q) : s'.arrs a = s.arrs a :=
  List.ext_getElem? fun q => (hF a).2 q (ha q)

theorem SolverArenasAt.frame {N M : ℕ} {s s' : State} {W : ℕ → ℕ → Prop}
    (h : SolverArenasAt N M s) (hF : Frame s s' W) : SolverArenasAt N M s' :=
  fun f hf => ((hF f.array).1).trans (h f hf)

theorem Common.step {N M : ℕ} {s₀ s s' : State} {W : ℕ → ℕ → Prop} (h : Common N M s₀ s)
    (hF : Frame s s' W) (hW50 : ∀ a q, W a q → 50 ≤ a) (hW : Words (N + M + 1) s')
    (hr : ∀ r : ℕ, r < 35 ∨ (35 < r ∧ r < 52) → s'.regs r = s.regs r) :
    Common N M s₀ s' :=
  ⟨fun a ha => (hF.arr_eq (a := a) fun q hq => by have := hW50 a q hq; omega).trans (h.1 a ha),
    fun r hr' => (hr r hr').trans (h.2.1 r hr'), hW, h.2.2.2.frame hF⟩

theorem PrefixAt.get {s : State} {a cap : ℕ} {xs : List ℕ} (h : PrefixAt s a cap xs) {i : ℕ}
    (hi : i < xs.length) : (s.arrs a)[i]? = some xs[i] := by
  rw [← List.getElem?_take_of_lt hi, h.2.2]; simp

theorem SolveInput.edges_le {N M w : ℕ} {search : Search} {s₀ : State}
    (hin : SolveInput N M w search s₀) : search.edges.size ≤ M := by
  have := hin.searchAt.2.2.2.2.2.2.2.2.1.2.1
  simpa using this

theorem SolveInput.edge {N M w : ℕ} {search : Search} {s₀ : State}
    (hin : SolveInput N M w search s₀) {i : ℕ} (hi : i < search.edges.size) :
    EdgeBounded N search.edges[i]! := hin.bounded.2.2.2.2.2.2 i hi

section reads

variable {N M w : ℕ} {search : Search} {s₀ s : State}

theorem head_read (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s) {i : ℕ}
    (hi : i < search.edges.size) :
    (s.arrs Field.head.array)[i]? = some search.edges[i]!.target := by
  rw [hc.1 _ (by simp [Field.array]), hin.searchAt.2.2.2.2.2.2.2.2.2.1.get (by simpa using hi)]
  simp [getElem!_pos search.edges i hi]

theorem tree_read (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s) {i : ℕ}
    (hi : i < search.edges.size) :
    (s.arrs Field.tree.array)[i]? = some search.edges[i]!.tree.toNat := by
  rw [hc.1 _ (by simp [Field.array]), hin.searchAt.2.2.2.2.2.2.2.2.2.2.1.get (by simpa using hi)]
  simp [getElem!_pos search.edges i hi]

theorem depth_read (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s) {v : ℕ}
    (hv : v < N) : (s.arrs Field.depth.array)[v]? = some (optionWord (search.depth[v]?.join)) := by
  have hsz := hin.searchAt.1
  rw [hc.1 _ (by simp [Field.array]), hin.searchAt.2.2.2.2.2.1.get (by simpa [hsz] using hv)]
  simp [hsz, hv]

theorem parent_read (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s) {v : ℕ}
    (hv : v < N) :
    (s.arrs Field.parent.array)[v]? = some (optionWord (search.parent[v]?.join)) := by
  have hsz := hin.searchAt.2.1
  rw [hc.1 _ (by simp [Field.array]), hin.searchAt.2.2.2.2.2.2.1.get (by simpa [hsz] using hv)]
  simp [hsz, hv]

theorem postorder_read (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s) {k : ℕ}
    (hk : k < search.postorder.length) :
    (s.arrs Field.postorder.array)[k]? = some search.postorder[k] := by
  rw [hc.1 _ (by simp [Field.array])]
  exact hin.searchAt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.get hk

end reads

theorem OutgoingChain.of_arrs_eq {s s' : State} {q : ℕ} {es : List ℕ}
    (h : OutgoingChain s q es)
    (he : s'.arrs Field.outgoingNext.array = s.arrs Field.outgoingNext.array) :
    OutgoingChain s' q es := by
  induction h with
  | nil => exact .nil
  | cons hn _ ih => exact .cons (he ▸ hn) ih

/-- The pointer of an outgoing list is zero or one more than its first edge. -/
theorem OutgoingChain.ptr_le {s : State} {q : ℕ} {es : List ℕ} (h : OutgoingChain s q es)
    {E : ℕ} (hes : ∀ i ∈ es, i < E) : q ≤ E := by
  cases h with
  | nil => omega
  | cons _ _ => have := hes _ List.mem_cons_self; omega

theorem OutgoingChain.eq_nil {s : State} {es : List ℕ} (h : OutgoingChain s 0 es) : es = [] := by
  cases h; rfl

/-! ### Slots -/

/-- Slot `v < N` holds the stored summary of `v`, slot `N` the current summary,
and slot `N + 1` the child summary. -/
def slotOf (N : ℕ) (results : Array (Option Summary)) (cur child : Option Summary) (v : ℕ) :
    Option Summary :=
  if v < N then results[v]! else if v = N then cur else child

/-- A pool for the slots of the solver. -/
def PoolOf (s : State) (N M : ℕ) (results : Array (Option Summary)) (cur child : Option Summary)
    (ptr : ℕ → ℕ) : Prop :=
  ∃ bsOf nsOf, PoolAt s M (N + 2) (slotOf N results cur child) ptr bsOf nsOf

/-- The result array holds the record pointers of the slots below `N`. -/
def ResultPtrs (s : State) (N : ℕ) (ptr : ℕ → ℕ) : Prop :=
  ∀ v < N, (s.arrs Field.result.array)[v]? = some (ptr v)

/-- The summaries between two rounds: no child, and the current summary at
record `pcur`. -/
def RepAt (s : State) (N M : ℕ) (results : Array (Option Summary)) (cur : Option Summary)
    (pcur : ℕ) : Prop :=
  ∃ ptr, PoolOf s N M results cur none ptr ∧ ptr N = pcur ∧ ptr (N + 1) = 0 ∧
    ResultPtrs s N ptr

theorem SolverArenasAt.len {N M : ℕ} {s : State} (h : SolverArenasAt N M s) (f : Field)
    (hf : f ∈ solverFields) : (s.arrs f.array).length = f.capacity N M := h f hf

theorem exec_stc {w : ℕ} {s : State} {a idx i : ℕ} (hidx : s.regs idx = i)
    (hi : i < (s.arrs a).length) (hiw : i < 2 ^ w) (hw : 0 < 2 ^ w) :
    Exec w (.write a (.reg idx) (.const 0)) s (s.writeArr a i 0) 3 := by
  subst hidx
  exact Exec.write (eval_reg hiw) (eval_const hw) hi

theorem exec_st' {w : ℕ} {s : State} {a idx val i v : ℕ} (hidx : s.regs idx = i)
    (hval : s.regs val = v) (hi : i < (s.arrs a).length) (hiw : i < 2 ^ w) (hvw : v < 2 ^ w) :
    Exec w (.write a (.reg idx) (.reg val)) s (s.writeArr a i v) 3 := by
  subst hidx hval
  exact exec_st hi hiw hvw

theorem exec_addc {w : ℕ} {s : State} {r : ℕ} (h : s.regs r + 1 < 2 ^ w) :
    Exec w (.assign r (.op .add (.reg r) (.const 1))) s (s.setReg r (s.regs r + 1)) 4 :=
  Exec.assign ((eval_op (eval_reg (by omega)) (eval_const (by omega))).trans (binop_add h))

theorem exec_subc {w : ℕ} {s : State} {dst r : ℕ} (h : s.regs r < 2 ^ w) (hw : 1 < 2 ^ w) :
    Exec w (.assign dst (.op .sub (.reg r) (.const 1))) s (s.setReg dst (s.regs r - 1)) 4 := by
  refine Exec.assign ((eval_op (eval_reg h) (eval_const (by omega))).trans ?_)
  simp [BinOp.eval, BinOp.raw, checkWord_of_lt (show s.regs r - 1 < 2 ^ w by omega)]

/-! ### The child of a back edge -/

/-- The singleton summary of a back edge `i` to depth `d`. -/
def leafSummary (d i : ℕ) : Summary := ⟨d, [⟨i, d⟩], []⟩

/-- `C := the singleton summary of back edge i`, with `i` in register 59 and
its head in register 60. The new return node is at register 53 and the new
record at register 55; both allocators move on. -/
def leafChildProg : Cmd :=
  .seq (.assign 72 (.read Field.depth.array (.reg 60)))
  (.seq (.assign 72 (.op .sub (.reg 72) (.const 1)))
  (.seq (.seq (.write Field.nodeEdge.array (.reg 53) (.reg 59))
    (.seq (.write Field.nodeDepth.array (.reg 53) (.reg 72))
    (.seq (.write Field.nodeNext.array (.reg 53) (.const 0))
    (.seq (.write Field.summaryLeast.array (.reg 55) (.reg 72))
    (.seq (.write Field.summaryFirst.array (.reg 55) (.reg 53))
    (.seq (.write Field.summaryLast.array (.reg 55) (.reg 53))
      (.write Field.summaryTop.array (.reg 55) (.const 0))))))))
  (.seq (.assign 61 (.reg 55))
  (.seq (.assign 53 (.op .add (.reg 53) (.const 1)))
    (.assign 55 (.op .add (.reg 55) (.const 1)))))))

theorem slotOf_child {N : ℕ} {results : Array (Option Summary)} {cur c c' : Option Summary}
    {v : ℕ} (hv : v < N + 2) (hne : v ≠ N + 1) :
    slotOf N results cur c v = slotOf N results cur c' v := by
  unfold slotOf
  by_cases h : v < N
  · simp [h]
  · have : v = N := by omega
    simp [this]

theorem leafChildProg_spec {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s)
    {results : Array (Option Summary)} {cur : Option Summary} {ptr : ℕ → ℕ}
    (hP : PoolOf s N M results cur none ptr) {i target : ℕ}
    (h59 : s.regs 59 = i) (hi : i < search.edges.size) (h60 : s.regs 60 = target)
    (ht : target < N) (h53 : 0 < s.regs 53) (h53M : s.regs 53 < M + 1)
    (h55 : 0 < s.regs 55) (h55M : s.regs 55 < M + 1) :
    ∃ s', Exec w leafChildProg s s' 38 ∧ Common N M s₀ s' ∧
      PoolOf s' N M results cur
        (some (leafSummary ((search.depth[target]?.join).getD 0) i))
        (Function.update ptr (N + 1) (s.regs 55)) ∧
      s'.regs 61 = s.regs 55 ∧ s'.regs 53 = s.regs 53 + 1 ∧ s'.regs 55 = s.regs 55 + 1 ∧
      s'.arrs Field.result.array = s.arrs Field.result.array ∧
      (∀ r : ℕ, r ≠ 53 → r ≠ 55 → r ≠ 61 → r ≠ 72 → s'.regs r = s.regs r) := by
  have hw := hin.word
  have hE := hin.edges_le
  set an := s.regs 53 with handef
  set p := s.regs 55 with hpdef
  set o := search.depth[target]?.join with hodef
  set d := o.getD 0 with hddef
  have hdN : d < N := by
    have hsz := hin.searchAt.1
    cases ho : o with
    | none => simp [hddef, ho]; omega
    | some d' =>
      have := hin.bounded.2.2.2.1 ⟨target, ht⟩ d' (by rw [← ho, hodef])
      simp [hddef, ho]; omega
  have hword : optionWord o ≤ N := by
    cases ho : o with
    | none => simp [optionWord]
    | some d' => simp [hddef, ho] at hdN; simp [optionWord]; omega
  -- Read the depth.
  let s₁ := s.setReg 72 (optionWord o)
  have hx₁ : Exec w (.assign 72 (.read Field.depth.array (.reg 60))) s s₁ 3 :=
    exec_ld (by omega) (by rw [h60]; exact depth_read hin hc ht) (by omega)
  let s₂ := s₁.setReg 72 d
  have hx₂ : Exec w (.assign 72 (.op .sub (.reg 72) (.const 1))) s₁ s₂ 4 := by
    have := exec_subc (w := w) (s := s₁) (dst := 72) (r := 72) (by simp [s₁]; omega) (by omega)
    simpa [s₂, s₁, optionWord_sub_one] using this
  have hr₂ : ∀ r, r ≠ 72 → s₂.regs r = s.regs r := fun r hr => by simp [s₂, s₁, hr]
  have g53 : s₂.regs 53 = an := by simp [s₂, s₁, handef]
  have g55 : s₂.regs 55 = p := by simp [s₂, s₁, hpdef]
  have g59 : s₂.regs 59 = i := by simp [s₂, s₁, h59]
  have g72 : s₂.regs 72 = d := by simp [s₂]
  -- The seven writes.
  have hlen : ∀ f ∈ solverFields, (s.arrs f.array).length = f.capacity N M := hc.2.2.2
  have hl50 : an < (s.arrs 50).length := by
    have := hlen Field.nodeEdge (by simp [solverFields]); simp [Field.array, Field.capacity] at this; omega
  have hl51 : an < (s.arrs 51).length := by
    have := hlen Field.nodeDepth (by simp [solverFields]); simp [Field.array, Field.capacity] at this; omega
  have hl52 : an < (s.arrs 52).length := by
    have := hlen Field.nodeNext (by simp [solverFields]); simp [Field.array, Field.capacity] at this; omega
  have hl58 : p < (s.arrs 58).length := by
    have := hlen Field.summaryLeast (by simp [solverFields]); simp [Field.array, Field.capacity] at this; omega
  have hl59 : p < (s.arrs 59).length := by
    have := hlen Field.summaryFirst (by simp [solverFields]); simp [Field.array, Field.capacity] at this; omega
  have hl60 : p < (s.arrs 60).length := by
    have := hlen Field.summaryLast (by simp [solverFields]); simp [Field.array, Field.capacity] at this; omega
  have hl61 : p < (s.arrs 61).length := by
    have := hlen Field.summaryTop (by simp [solverFields]); simp [Field.array, Field.capacity] at this; omega
  let s₃ := s₂.writeArr 50 an i
  let s₄ := s₃.writeArr 51 an d
  let s₅ := s₄.writeArr 52 an 0
  let s₆ := s₅.writeArr 58 p d
  let s₇ := s₆.writeArr 59 p an
  let s₈ := s₇.writeArr 60 p an
  let s₉ := s₈.writeArr 61 p 0
  have hx₉ : Exec w (.seq (.write Field.nodeEdge.array (.reg 53) (.reg 59))
      (.seq (.write Field.nodeDepth.array (.reg 53) (.reg 72))
      (.seq (.write Field.nodeNext.array (.reg 53) (.const 0))
      (.seq (.write Field.summaryLeast.array (.reg 55) (.reg 72))
      (.seq (.write Field.summaryFirst.array (.reg 55) (.reg 53))
      (.seq (.write Field.summaryLast.array (.reg 55) (.reg 53))
        (.write Field.summaryTop.array (.reg 55) (.const 0)))))))) s₂ s₉ 21 := by
    have e3 := exec_st' (w := w) (s := s₂) (a := 50) (idx := 53) (val := 59) g53 g59 (by simp [s₂, s₁]; omega)
      (by omega) (by omega)
    have e4 := exec_st' (w := w) (s := s₃) (a := 51) (idx := 53) (val := 72) g53 g72 (by simp [s₃, s₂, s₁]; omega)
      (by omega) (by omega)
    have e5 := exec_stc (w := w) (s := s₄) (a := 52) (idx := 53) g53 (by simp [s₄, s₃, s₂, s₁]; omega)
      (by omega) (by omega)
    have e6 := exec_st' (w := w) (s := s₅) (a := 58) (idx := 55) (val := 72) g55 g72
      (by simp [s₅, s₄, s₃, s₂, s₁]; omega) (by omega) (by omega)
    have e7 := exec_st' (w := w) (s := s₆) (a := 59) (idx := 55) (val := 53) g55 g53
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁]; omega) (by omega) (by omega)
    have e8 := exec_st' (w := w) (s := s₇) (a := 60) (idx := 55) (val := 53) g55 g53
      (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁]; omega) (by omega) (by omega)
    have e9 := exec_stc (w := w) (s := s₈) (a := 61) (idx := 55) g55
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]; omega) (by omega) (by omega)
    exact Exec.seq e3 (Exec.seq e4 (Exec.seq e5 (Exec.seq e6 (Exec.seq e7 (Exec.seq e8 e9)))))
  -- The register updates.
  let s₁₀ := s₉.setReg 61 p
  let s₁₁ := s₁₀.setReg 53 (an + 1)
  let s₁₂ := s₁₁.setReg 55 (p + 1)
  have hx₁₂ : Exec w (.seq (.assign 61 (.reg 55)) (.seq (.assign 53 (.op .add (.reg 53) (.const 1)))
      (.assign 55 (.op .add (.reg 55) (.const 1))))) s₉ s₁₂ 10 := by
    have e10 : Exec w (.assign 61 (.reg 55)) s₉ s₁₀ 2 := by
      have := exec_mov (w := w) (s := s₉) (dst := 61) (src := 55) (by
        show s₂.regs 55 < 2 ^ w; omega)
      rw [show s₉.regs 55 = p from g55] at this
      exact this
    have e11 : Exec w (.assign 53 (.op .add (.reg 53) (.const 1))) s₁₀ s₁₁ 4 := by
      have h : s₁₀.regs 53 = an := by simp [s₁₀]; exact g53
      have := exec_addc (w := w) (s := s₁₀) (r := 53) (by rw [h]; omega)
      rw [h] at this; exact this
    have e12 : Exec w (.assign 55 (.op .add (.reg 55) (.const 1))) s₁₁ s₁₂ 4 := by
      have h : s₁₁.regs 55 = p := by simp [s₁₁, s₁₀]; exact g55
      have := exec_addc (w := w) (s := s₁₁) (r := 55) (by rw [h]; omega)
      rw [h] at this; exact this
    exact Exec.seq e10 (Exec.seq e11 e12)
  have hx := Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₉ hx₁₂))
  -- The frame.
  let W : ℕ → ℕ → Prop := fun a q => q = an ∧ (a = 50 ∨ a = 51 ∨ a = 52) ∨
    q = p ∧ (a = 58 ∨ a = 59 ∨ a = 60 ∨ a = 61)
  have hF₉ : Frame s₂ s₉ W :=
    (((((((Frame.writeArr s₂ _ _ _).trans (Frame.writeArr s₃ _ _ _)).trans
      (Frame.writeArr s₄ _ _ _)).trans (Frame.writeArr s₅ _ _ _)).trans
      (Frame.writeArr s₆ _ _ _)).trans (Frame.writeArr s₇ _ _ _)).trans
      (Frame.writeArr s₈ _ _ _)).mono (by
        intro a q h
        rcases h with ((((((h | h) | h) | h) | h) | h) | h) <;> simp [W, h.1, h.2])
  have hF : Frame s s₁₂ W := hF₉
  have hW50 : ∀ a q, W a q → 50 ≤ a := by
    intro a q h; simp only [W] at h; omega
  have hWD : Words (N + M + 1) s₁₂ := by
    have hW₂ : Words (N + M + 1) s₂ := hc.2.2.1
    exact ((((((hW₂.writeArr _ _ (by omega)).writeArr _ _ (by omega)).writeArr _ _
      (by omega)).writeArr _ _ (by omega)).writeArr _ _ (by omega)).writeArr _ _
      (by omega)).writeArr _ _ (by omega)
  have hregs : ∀ r : ℕ, r ≠ 53 → r ≠ 55 → r ≠ 61 → r ≠ 72 → s₁₂.regs r = s.regs r := by
    intro r h1 h2 h3 h4
    simp [s₁₂, s₁₁, s₁₀, h1, h2, h3]
    exact hr₂ r h4
  have r53 : s₁₂.regs 53 = an + 1 := by simp [s₁₂, s₁₁]
  have r55 : s₁₂.regs 55 = p + 1 := by simp [s₁₂]
  have r54 : s₁₂.regs 54 = s.regs 54 := hregs 54 (by decide) (by decide) (by decide) (by decide)
  refine ⟨s₁₂, hx, hc.step hF hW50 hWD fun r hr => hregs r (by omega) (by omega) (by omega)
    (by omega), ?_, by simp [s₁₂, s₁₁, s₁₀], by simp [s₁₂, s₁₁], by simp [s₁₂],
    ?_, hregs⟩
  rotate_left
  · show s₉.arrs 62 = s.arrs 62
    simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  -- The pool.
  obtain ⟨bsOf, nsOf, hpool⟩ := hP
  have hb := hpool.2.1
  refine ⟨Function.update bsOf (N + 1) [], Function.update nsOf (N + 1) [an], ?_⟩
  refine PoolAt.update (· = N + 1) hpool hF (by omega) (by omega) (by omega)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v hv hT
    exact ⟨slotOf_child hv hT, Function.update_of_ne hT _ _, Function.update_of_ne hT _ _,
      Function.update_of_ne hT _ _⟩
  · intro v hv hT
    obtain ⟨hn, hbk, hpt⟩ := hb v hv
    refine ⟨fun _ h => ?_, fun q _ h => ?_, fun q hq h => ?_⟩
    · simp [SummaryCell, W, Field.array] at h; omega
    · simp [BlockCell, W, Field.array] at h
    · have := hn q hq; simp [NodeCell, W, Field.array] at h; omega
  · intro v hv hT
    subst hT
    simp only [Function.update_self]
    refine ⟨?_, by simp [r53], by simp, by simp [r55]⟩
    simp only [slotOf, show ¬ N + 1 < N by omega, show N + 1 ≠ N by omega, ↓reduceIte,
      OptSummaryAt, leafSummary]
    refine ⟨by omega, by omega, ?_, an, an, 0, [an], [], ?_, ?_, ?_,
      ⟨NodeChain.cons (by omega) (by omega) ?_ ?_ ?_ NodeChain.nil, by simp, by simp⟩,
      BlockChain.nil, by simp, by simp, List.nodup_nil⟩
    all_goals simp [s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Field.array, hl50, hl51,
      hl52, hl58, hl59, hl60, hl61]
  · intro v hv hT q hq
    subst hT
    simp at hq
    exact Or.inr (by omega)
  · intro v hv hT q hq
    subst hT
    simp at hq
  · intro v hv hT _
    subst hT
    exact Or.inr (by simp [hpdef])
  · intro u hu v hv hTu hTv huv
    exact absurd (hTu.trans hTv.symm) huv

/-! ### The child of a tree edge -/

theorem getElem!_set! (results : Array (Option Summary)) (t v : ℕ) (x : Option Summary)
    (ht : t < results.size) : (results.set! t x)[v]! = if v = t then x else results[v]! := by
  by_cases hv : v = t
  · subst hv; simp [ht]
  · simp only [hv, ↓reduceIte]
    by_cases hvs : v < results.size
    · simp [getElem!_pos, hvs, Ne.symm hv]
    · rw [getElem!_neg _ v (by simpa using hvs), getElem!_neg _ v hvs]

/-- `C := result[target]; result[target] := 0`, with the target in register 60.
The stored summary of the target moves to the child slot. -/
def treeChildMoveProg : Cmd :=
  .seq (.assign 61 (.read Field.result.array (.reg 60)))
    (.write Field.result.array (.reg 60) (.const 0))

theorem treeChildMoveProg_spec {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s)
    {results : Array (Option Summary)} {cur : Option Summary} {ptr : ℕ → ℕ}
    (hP : PoolOf s N M results cur none ptr) (hR : ResultPtrs s N ptr) (hsz : results.size = N)
    {target : ℕ} (h60 : s.regs 60 = target) (ht : target < N) (h55 : 0 < s.regs 55) :
    ∃ s', Exec w treeChildMoveProg s s' 6 ∧ Common N M s₀ s' ∧
      PoolOf s' N M (results.set! target none) cur results[target]!
        (Function.update (Function.update ptr (N + 1) (ptr target)) target 0) ∧
      ResultPtrs s' N (Function.update (Function.update ptr (N + 1) (ptr target)) target 0) ∧
      s'.regs 61 = ptr target ∧ (∀ r : ℕ, r ≠ 61 → s'.regs r = s.regs r) := by
  have hw := hin.word
  have hlen : (s.arrs Field.result.array).length = N := by
    have := hc.2.2.2 Field.result (by simp [solverFields]); simpa [Field.capacity] using this
  have hread : (s.arrs Field.result.array)[target]? = some (ptr target) := hR target ht
  have hpw : ptr target ≤ N + M + 1 := hc.2.2.1.get (by simp [Field.array]) (by simp [Field.array])
    hread
  let s₁ := s.setReg 61 (ptr target)
  let s₂ := s₁.writeArr Field.result.array target 0
  have hx : Exec w treeChildMoveProg s s₂ 6 := by
    have e1 : Exec w (.assign 61 (.read Field.result.array (.reg 60))) s s₁ 3 :=
      exec_ld (by omega) (by rw [h60]; exact hread) (by omega)
    have e2 : Exec w (.write Field.result.array (.reg 60) (.const 0)) s₁ s₂ 3 :=
      exec_stc (by simp [s₁, h60]) (by simp [s₁]; omega) (by omega) (by omega)
    exact Exec.seq e1 e2
  let W : ℕ → ℕ → Prop := fun a q => a = Field.result.array ∧ q = target
  have hF : Frame s s₂ W := (Frame.writeArr s₁ _ _ _).mono fun a q h => by simp [W, h.1, h.2]
  have hregs : ∀ r : ℕ, r ≠ 61 → s₂.regs r = s.regs r := fun r hr => by simp [s₂, s₁, hr]
  refine ⟨s₂, hx, hc.step hF (fun a q h => by simp [W, Field.array] at h; omega)
    (hc.2.2.1.writeArr _ _ (by omega)) (fun r hr => hregs r (by omega)), ?_, ?_,
    by simp [s₂, s₁], hregs⟩
  · obtain ⟨bsOf, nsOf, hpool⟩ := hP
    have hb := hpool.2.1
    have hd := hpool.2.2
    refine ⟨Function.update (Function.update bsOf (N + 1) (bsOf target)) target [],
      Function.update (Function.update nsOf (N + 1) (nsOf target)) target [], ?_⟩
    have hsl : ∀ v < N + 2, slotOf N (results.set! target none) cur results[target]! v =
        if v = target then none else if v = N + 1 then results[target]! else
          slotOf N results cur none v := by
      intro v hv
      unfold slotOf
      rw [getElem!_set! _ _ _ _ (by omega)]
      by_cases h1 : v = target
      · simp [h1, ht]
      · by_cases h2 : v < N
        · simp [h1, h2, show v ≠ N + 1 by omega]
        · by_cases h3 : v = N
          · subst h3
            simp [h1]
          · obtain rfl : v = N + 1 := by omega
            simp [show N + 1 ≠ target by omega]
    refine PoolAt.update (fun v => v = target ∨ v = N + 1) hpool hF (le_refl _) (le_refl _)
      (le_refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro v hv hT
      push Not at hT
      rw [hsl v hv]
      simp [hT.1, hT.2, Function.update_of_ne]
    · intro v hv hT
      refine ⟨fun _ h => ?_, fun q _ h => ?_, fun q _ h => ?_⟩ <;>
        simp [SummaryCell, BlockCell, NodeCell, W, Field.array] at h
    · intro v hv hT
      rcases hT with rfl | rfl
      · simp only [Function.update_self, hsl _ hv, ↓reduceIte]
        exact ⟨⟨rfl, rfl, rfl⟩, by simp, by simp, by simp [s₂, s₁]; omega⟩
      · simp only [Function.update_of_ne (show N + 1 ≠ target by omega), Function.update_self,
          hsl _ hv, show N + 1 ≠ target by omega, ↓reduceIte]
        refine ⟨?_, (hb target (by omega)).1, (hb target (by omega)).2.1, (hb target (by omega)).2.2⟩
        have h := hpool.1 target (by omega)
        simp only [slotOf, ht, ↓reduceIte] at h
        refine h.frame hF (fun _ h => ?_) (fun q _ h => ?_) (fun q _ h => ?_) <;>
          simp [SummaryCell, BlockCell, NodeCell, W, Field.array] at h
    · intro v hv hT q hq
      rcases hT with rfl | rfl
      · simp at hq
      · simp only [Function.update_of_ne (show N + 1 ≠ target by omega), Function.update_self] at hq
        exact Or.inl ⟨target, by omega, Or.inl rfl, hq⟩
    · intro v hv hT q hq
      rcases hT with rfl | rfl
      · simp at hq
      · simp only [Function.update_of_ne (show N + 1 ≠ target by omega), Function.update_self] at hq
        exact Or.inl ⟨target, by omega, Or.inl rfl, hq⟩
    · intro v hv hT hp
      rcases hT with rfl | rfl
      · simp at hp
      · simp only [Function.update_of_ne (show N + 1 ≠ target by omega), Function.update_self]
          at hp ⊢
        exact Or.inl ⟨target, by omega, Or.inl rfl, hp, rfl⟩
    · intro u hu v hv hTu hTv huv
      rcases hTu with hu' | hu' <;> rcases hTv with hv' | hv' <;> subst u v
      · exact absurd rfl huv
      · simp
      · simp only [Function.update_self, Function.update_of_ne (show N + 1 ≠ target by omega)]
        simp
      · exact absurd rfl huv
  · intro v hv
    simp only [s₂, s₁]
    by_cases h : v = target
    · subst h
      have hlen62 : (s.arrs 62).length = N := hlen
      simp [State.writeArr, State.setArr, hlen62, ht, Field.array]
    · rw [Function.update_of_ne h, Function.update_of_ne (show v ≠ N + 1 by omega)]
      have := hR v hv
      simp [State.writeArr, State.setArr, Field.array, Ne.symm h] at this ⊢
      exact this

end GraphMinor.Compute.PlanarityRam
