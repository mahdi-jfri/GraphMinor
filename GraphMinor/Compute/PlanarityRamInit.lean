module

public import GraphMinor.Compute.PlanarityRamLayout

/-!
# Fixed-capacity allocation for the left-right test

Part V, Section 1 allocates each arena once. The commands here use the input
vertex count in register 30 and the counted adjacency entries in register 36.
The allocation proof works for any list of fields and bounds each allocation
by the same linear bound. No old scratch-array length enters that bound.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- The capacity expression for each fixed field. -/
def Field.capacityExpr : Field → Expr
  | .depth | .parent | .parentEdge | .frameVertex | .frameNext | .postorder
  | .outgoingFirst | .outgoingLast | .result => .reg 30
  | .bucket => .op .add (.op .mul (.const 2) (.reg 30)) (.const 1)
  | .nodeEdge | .nodeDepth | .nodeNext
  | .blockLeftFirst | .blockLeftLast | .blockRightFirst | .blockRightLast | .blockBelow
  | .summaryLeast | .summaryFirst | .summaryLast | .summaryTop =>
    .op .add (.reg 36) (.const 1)
  | _ => .reg 36

/-- Allocate fields in their fixed order. -/
def allocateFields : List Field → Cmd
  | [] => .skip
  | f :: fs => .seq (.alloc f.array f.capacityExpr) (allocateFields fs)

/-- The state after those allocations, with no change to any register. -/
def allocatedState (N M : ℕ) : List Field → State → State
  | [], s => s
  | f :: fs, s => allocatedState N M fs (s.setArr f.array (List.replicate (f.capacity N M) 0))

/-- Exact instruction count for these allocations. -/
def allocationTime (N M : ℕ) : List Field → ℕ
  | [] => 1
  | f :: fs => f.capacityExpr.cost + f.capacity N M + allocationTime N M fs

/-- Capacity expressions need only linear-size words, including their
intermediate values. -/
theorem Field.capacityExpr_eval (f : Field) (N M w : ℕ) (s : State)
    (hN : s.regs 30 = N) (hM : s.regs 36 = M)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    f.capacityExpr.eval w s = some (f.capacity N M) := by
  have hn : N < 2 ^ w := by omega
  have hm : M < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hprod : 2 * N < 2 ^ w := by omega
  have hbucket : 2 * N + 1 < 2 ^ w := by omega
  have hnode : M + 1 < 2 ^ w := by omega
  cases f <;>
    simp [Field.capacityExpr, Field.capacity, Expr.eval, hN, hM, BinOp.eval,
      BinOp.raw, checkWord_of_lt, hn, hm, htwo, hone, hprod, hbucket, hnode]

/-- Allocation preserves every register. -/
theorem allocatedState_regs (N M : ℕ) (fs : List Field) (s : State) :
    (allocatedState N M fs s).regs = s.regs := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih => exact ih _

/-- Allocations preserve all arrays absent from the field list. -/
theorem allocatedState_arrs_of_not_mem (N M a : ℕ) (fs : List Field) (s : State)
    (h : ∀ f ∈ fs, a ≠ f.array) :
    (allocatedState N M fs s).arrs a = s.arrs a := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    rw [allocatedState, ih _ (fun g hg => h g (by simp [hg]))]
    exact State.setArr_arrs_ne _ _ (h f (by simp))

/-- Each allocation executes with its new capacity charged exactly once. -/
theorem allocateFields_exec (fs : List Field) (N M w : ℕ) (s : State)
    (hN : s.regs 30 = N) (hM : s.regs 36 = M)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    Exec w (allocateFields fs) s (allocatedState N M fs s) (allocationTime N M fs) := by
  induction fs generalizing s with
  | nil => exact Exec.skip s
  | cons f fs ih =>
    exact Exec.seq (Exec.alloc (f.capacityExpr_eval N M w s hN hM hw))
      (ih _ hN hM)

/-- All allocation time is linear for a fixed field list. -/
theorem allocationTime_le (fs : List Field) (N M : ℕ) :
    allocationTime N M fs ≤ fs.length * (2 * (N + M + 1) + 7) + 1 := by
  induction fs with
  | nil => simp [allocationTime]
  | cons f fs ih =>
    have hc : f.capacityExpr.cost ≤ 7 := by cases f <;> decide
    have hf := f.capacity_le N M
    simp only [allocationTime, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The allocation program cannot alter the calling convention's protected arrays. -/
theorem allocatedState_preserves (N M : ℕ) (fs : List Field) (s : State) :
    (∀ r, (allocatedState N M fs s).regs r = s.regs r) ∧
    (∀ a < 33, (allocatedState N M fs s).arrs a = s.arrs a) := by
  refine ⟨fun r => congrFun (allocatedState_regs N M fs s) r, ?_⟩
  intro a ha
  apply allocatedState_arrs_of_not_mem
  intro f _ heq
  rw [heq] at ha
  exact (Nat.not_lt_of_ge f.array_ge) ha

/-- Allocated fields have their full capacity and all words initially zero. -/
theorem allocatedState_arrs_of_mem (N M : ℕ) (fs : List Field) (s : State)
    (f : Field) (hf : f ∈ fs) :
    (allocatedState N M fs s).arrs f.array = List.replicate (f.capacity N M) 0 := by
  induction fs generalizing s with
  | nil => simp at hf
  | cons g gs ih =>
    simp only [allocatedState]
    by_cases ht : f ∈ gs
    · exact ih _ ht
    · rw [allocatedState_arrs_of_not_mem N M f.array gs _ (by
        intro k hk heq
        have he := Field.array_injective heq
        subst k
        exact ht hk)]
      have he : f = g := (List.mem_cons.mp hf).resolve_right ht
      subst g
      exact State.setArr_arrs_self _ _ _

/-- The arenas required for the first search, in allocation order. -/
def searchFields : List Field :=
  [.depth, .parent, .parentEdge, .tail, .head, .tree, .low, .low2, .key,
    .frameVertex, .frameNext, .postorder]

/-- Allocate search arenas and clear the edge, frame, and postorder counters. -/
def initializeSearchProg : Cmd :=
  .seq (allocateFields searchFields)
    (.seq (.assign 37 (.const 0))
      (.seq (.assign 38 (.const 0)) (.assign 39 (.const 0))))

/-- The resulting state of search initialization. -/
def initializedSearchState (N M : ℕ) (s : State) : State :=
  (((allocatedState N M searchFields s).setReg 37 0).setReg 38 0).setReg 39 0

/-- The initialized arrays represent exactly `initialSearch N`. This fact
concerns the representation and needs no graph or word-size hypothesis. -/
theorem initializedSearchState_searchAt (N M : ℕ) (s : State) :
    SearchAt N M (initializedSearchState N M s) (LRPlanarity.initialSearch N) := by
  have ha (f : Field) (hf : f ∈ searchFields) :
      (initializedSearchState N M s).arrs f.array =
        List.replicate (f.capacity N M) 0 := by
    exact allocatedState_arrs_of_mem N M searchFields s f hf
  simp only [SearchAt, LRPlanarity.initialSearch]
  simp only [Array.size_replicate, Array.size_empty, List.length_nil]
  refine ⟨True.intro, True.intro, True.intro, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initializedSearchState, State.setReg]
  · simp [initializedSearchState]
  all_goals simp [PrefixAt, Field.capacity, optionWord,
    ha .depth (by simp [searchFields]),
    ha .parent (by simp [searchFields]),
    ha .parentEdge (by simp [searchFields]),
    ha .tail (by simp [searchFields]),
    ha .head (by simp [searchFields]),
    ha .tree (by simp [searchFields]),
    ha .low (by simp [searchFields]),
    ha .low2 (by simp [searchFields]),
    ha .key (by simp [searchFields]),
    ha .postorder (by simp [searchFields])]

/-- Initialization also represents the empty explicit-frame stack. -/
theorem initializedSearchState_framesAt (N M : ℕ) (s : State) :
    FramesAt N (initializedSearchState N M s) [] := by
  have hv := allocatedState_arrs_of_mem N M searchFields s .frameVertex
    (by simp [searchFields])
  have hn := allocatedState_arrs_of_mem N M searchFields s .frameNext
    (by simp [searchFields])
  simp [FramesAt, initializedSearchState, PrefixAt, hv, hn, Field.capacity]

/-- Initialization changes only the three counters and work arrays. -/
theorem initializedSearchState_preserves (N M : ℕ) (s : State) :
    (∀ r : ℕ, r ≠ 37 → r ≠ 38 → r ≠ 39 →
      (initializedSearchState N M s).regs r = s.regs r) ∧
    (∀ a < 33, (initializedSearchState N M s).arrs a = s.arrs a) := by
  refine ⟨?_, (allocatedState_preserves N M searchFields s).2⟩
  intro r h37 h38 h39
  simp [initializedSearchState, h37, h38, h39, allocatedState_regs]

/-- Initialization executes in linear time, including allocation. -/
theorem initializeSearchProg_exec (N M w : ℕ) (s : State)
    (hN : s.regs 30 = N) (hM : s.regs 36 = M)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    ∃ t, Exec w initializeSearchProg s (initializedSearchState N M s) t ∧
      t ≤ 120 * (N + M + 1) := by
  have hz : 0 < 2 ^ w := by omega
  refine ⟨allocationTime N M searchFields + 6, ?_, ?_⟩
  · exact Exec.seq (allocateFields_exec searchFields N M w s hN hM hw)
      (Exec.seq (Exec.assign (e := .const 0) (checkWord_of_lt hz))
        (Exec.seq (Exec.assign (e := .const 0) (checkWord_of_lt hz))
          (Exec.assign (e := .const 0) (checkWord_of_lt hz))))
  · have ht := allocationTime_le searchFields N M
    simp only [searchFields, List.length_cons, List.length_nil] at ht ⊢
    omega

end GraphMinor.Compute.PlanarityRam
