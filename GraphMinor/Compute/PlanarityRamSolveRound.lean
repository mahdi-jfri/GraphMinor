module

public import GraphMinor.Compute.PlanarityRamSolveEdge
import GraphMinor.Compute.WhileRounds

/-!
# One round of the edge loop

This file proves that one round of the RAM edge loop refines one step of
`solveOutgoing`:

    i := the next outgoing edge of v
    C := the child summary of i      (the stored summary of a tree edge's head,
                                       or a singleton for a back edge)
    S := MERGE(S, C)

The round has three parts: reading the edge record, building the child
(`childProg_spec`), and the merge (`mergeStep`). `edgeRound` puts them
together and pays for the round with a potential: a constant per remaining
edge plus the weights of all live summaries.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-! ### One step of `solveOutgoing` -/

/-- The child summary of edge `i` in `solveOutgoing`. -/
def edgeChild (search : Search) (i : ℕ) (results : Array (Option Summary)) : Option Summary :=
  if search.edges[i]!.tree then results[search.edges[i]!.target]!
  else some (leafSummary ((search.depth[search.edges[i]!.target]?.join).getD 0) i)

/-- The stored summaries after edge `i` in `solveOutgoing`: a tree edge takes
the summary of its head. -/
def edgeResults (search : Search) (i : ℕ) (results : Array (Option Summary)) :
    Array (Option Summary) :=
  if search.edges[i]!.tree then results.set! search.edges[i]!.target none else results

theorem solveOutgoing_cons (search : Search) (i : ℕ) (rest : List ℕ)
    (results : Array (Option Summary)) (summary : Option Summary) :
    solveOutgoing search (i :: rest) results summary =
      (merge summary (edgeChild search i results)).bind
        (solveOutgoing search rest (edgeResults search i results)) := by
  simp only [solveOutgoing, edgeChild, edgeResults, leafSummary]
  split <;> rfl

/-! ### Moving pools between states -/

theorem OptSummaryAt.of_arrs_eq {s s' : State} {M p : ℕ} {o : Option Summary} {bs ns : List ℕ}
    (h : OptSummaryAt s M p o bs ns) (he : s'.arrs = s.arrs) : OptSummaryAt s' M p o bs ns :=
  h.frame (Frame.of_arrs_eq he (fun _ _ => False)) (fun _ h => by simp [SummaryCell] at h)
    (fun _ _ h => by simp [BlockCell] at h) (fun _ _ h => by simp [NodeCell] at h)

theorem PoolAt.congr {s s' : State} {M K : ℕ} {sl : ℕ → Option Summary} {ptr : ℕ → ℕ}
    {bsOf nsOf : ℕ → List ℕ} (h : PoolAt s M K sl ptr bsOf nsOf) (he : s'.arrs = s.arrs)
    (h53 : s'.regs 53 = s.regs 53) (h54 : s'.regs 54 = s.regs 54)
    (h55 : s'.regs 55 = s.regs 55) : PoolAt s' M K sl ptr bsOf nsOf :=
  ⟨fun v hv => (h.1 v hv).of_arrs_eq he, by rw [h53, h54, h55]; exact h.2.1, h.2.2⟩

theorem PoolOf.congr {s s' : State} {N M : ℕ} {results : Array (Option Summary)}
    {cur child : Option Summary} {ptr : ℕ → ℕ} (h : PoolOf s N M results cur child ptr)
    (he : s'.arrs = s.arrs) (h53 : s'.regs 53 = s.regs 53) (h54 : s'.regs 54 = s.regs 54)
    (h55 : s'.regs 55 = s.regs 55) : PoolOf s' N M results cur child ptr := by
  obtain ⟨bsOf, nsOf, h⟩ := h
  exact ⟨bsOf, nsOf, h.congr he h53 h54 h55⟩

/-! ### The child -/

/-- The child step: a tree edge takes the stored summary of its head, a back
edge builds a singleton summary. The tree flag is in register 73. -/
def childProg : Cmd := .ite (.reg 73) treeChildMoveProg leafChildProg

theorem childProg_spec {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s)
    {results : Array (Option Summary)} {cur : Option Summary} {ptr : ℕ → ℕ}
    (hP : PoolOf s N M results cur none ptr) (hR : ResultPtrs s N ptr) (hsz : results.size = N)
    {i : ℕ} (h59 : s.regs 59 = i) (hi : i < search.edges.size)
    (h60 : s.regs 60 = search.edges[i]!.target) (h73 : s.regs 73 = search.edges[i]!.tree.toNat)
    (h53 : 0 < s.regs 53) (h53M : s.regs 53 < M + 1)
    (h55 : 0 < s.regs 55) (h55M : s.regs 55 < M + 1) :
    ∃ s' t ptr', Exec w childProg s s' t ∧ t ≤ 39 ∧ Common N M s₀ s' ∧
      PoolOf s' N M (edgeResults search i results) cur (edgeChild search i results) ptr' ∧
      ResultPtrs s' N ptr' ∧ ptr' N = ptr N ∧ s'.regs 61 = ptr' (N + 1) ∧
      (∀ r : ℕ, r ≠ 53 → r ≠ 55 → r ≠ 61 → r ≠ 72 → s'.regs r = s.regs r) ∧
      s.regs 53 ≤ s'.regs 53 ∧ s'.regs 53 ≤ s.regs 53 + 1 ∧
      s.regs 55 ≤ s'.regs 55 ∧ s'.regs 55 ≤ s.regs 55 + 1 ∧
      arraySum weight (edgeResults search i results) + weight (edgeChild search i results) ≤
        arraySum weight results + 10 ∧
      (edgeResults search i results).size = N := by
  have hw := hin.word
  have ht : search.edges[i]!.target < N := (hin.edge hi).2.1
  by_cases htree : search.edges[i]!.tree
  · have h73' : s.regs 73 = 1 := by simp [h73, htree]
    obtain ⟨s', hx, hc', hP', hR', h61, hregs⟩ :=
      treeChildMoveProg_spec hin hc hP hR hsz h60 ht h55
    refine ⟨s', _, Function.update (Function.update ptr (N + 1) (ptr search.edges[i]!.target))
      search.edges[i]!.target 0, exec_ite_pos (c₂ := leafChildProg) (by omega) (by omega) hx, by omega, hc',
      ?_, ?_, ?_, ?_, fun r h1 h2 h3 _ => hregs r h3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [edgeResults, edgeChild, htree] using hP'
    · exact hR'
    · rw [Function.update_of_ne (show N ≠ search.edges[i]!.target by omega),
        Function.update_of_ne (show N ≠ N + 1 by omega)]
    · rw [h61, Function.update_of_ne (show N + 1 ≠ search.edges[i]!.target by omega),
        Function.update_self]
    · rw [hregs 53 (by decide)]
    · rw [hregs 53 (by decide)]; omega
    · rw [hregs 55 (by decide)]
    · rw [hregs 55 (by decide)]; omega
    · have := arraySum_set weight results search.edges[i]!.target none (by omega)
      simp only [edgeResults, edgeChild, htree, ↓reduceIte]
      simp only [weight] at this ⊢
      omega
    · simp [edgeResults, htree, hsz]
  · have h73' : s.regs 73 = 0 := by simp [h73, htree]
    have hP0 := hP
    obtain ⟨bsOf, nsOf, hpool⟩ := hP0
    obtain ⟨s', hx, hc', hP', h61, h53', h55', h62, hregs⟩ :=
      leafChildProg_spec hin hc hP h59 hi h60 ht h53 h53M h55 h55M
    refine ⟨s', _, Function.update ptr (N + 1) (s.regs 55),
      exec_ite_zero (c₁ := treeChildMoveProg) h73' hx, by omega, hc', ?_, ?_, ?_, ?_, hregs,
      by omega, by omega, by omega, by omega, ?_, ?_⟩
    · simpa [edgeResults, edgeChild, htree] using hP'
    · intro v hv
      rw [Function.update_of_ne (show v ≠ N + 1 by omega)]
      have := hR v hv
      rwa [h62]
    · rw [Function.update_of_ne (show N ≠ N + 1 by omega)]
    · rw [h61, Function.update_self]
    · simp [edgeResults, edgeChild, htree, weight, leafSummary, nodeCount, stackNodes]
    · simp [edgeResults, htree, hsz]

/-! ### The merge -/

theorem Common.blockLen {N M : ℕ} {s₀ s : State} (hc : Common N M s₀ s) {a : ℕ}
    (ha : IsBlockArr a) : (s.arrs a).length = M + 1 := by
  have h := hc.2.2.2
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · simpa [Field.capacity] using h Field.blockLeftFirst (by simp [solverFields])
  · simpa [Field.capacity] using h Field.blockLeftLast (by simp [solverFields])
  · simpa [Field.capacity] using h Field.blockRightFirst (by simp [solverFields])
  · simpa [Field.capacity] using h Field.blockRightLast (by simp [solverFields])
  · simpa [Field.capacity] using h Field.blockBelow (by simp [solverFields])

theorem slotOf_lt {N : ℕ} {results : Array (Option Summary)} {cur child : Option Summary}
    {v : ℕ} (hv : v < N) : slotOf N results cur child v = results[v]! := by
  simp [slotOf, hv]

theorem slotOf_self {N : ℕ} {results : Array (Option Summary)} {cur child : Option Summary} :
    slotOf N results cur child N = cur := by
  simp [slotOf]

theorem slotOf_succ {N : ℕ} {results : Array (Option Summary)} {cur child : Option Summary} :
    slotOf N results cur child (N + 1) = child := by
  simp [slotOf]

/-- The merge step: `S := MERGE(S, C)` with the current summary at register
57 and the child at register 61. -/
theorem mergeStep {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s)
    {results : Array (Option Summary)} {cur child : Option Summary} {ptr : ℕ → ℕ}
    (hP : PoolOf s N M results cur child ptr) (hR : ResultPtrs s N ptr)
    (h57 : s.regs 57 = ptr N) (h61 : s.regs 61 = ptr (N + 1)) (h35 : s.regs 35 = 1)
    (h54 : 0 < s.regs 54) (h54M : s.regs 54 < M + 1) (h55 : 0 < s.regs 55) :
    ∃ s' t, Exec w mergeProg s s' t ∧ Common N M s₀ s' ∧
      (∀ r : ℕ, r ≠ 35 → r ≠ 54 → r ≠ 57 → (r < 62 ∨ 74 < r) → s'.regs r = s.regs r) ∧
      s.regs 54 ≤ s'.regs 54 ∧ s'.regs 54 ≤ s.regs 54 + 1 ∧
      match merge cur child with
      | none => s'.regs 35 = 0 ∧ t ≤ 300 + 120 * (blockCount cur + blockCount child)
      | some m => s'.regs 35 = 1 ∧ RepAt s' N M results m (s'.regs 57) ∧
          t + weight m ≤ 300 + weight cur + weight child := by
  have hw := hin.word
  obtain ⟨bsOf, nsOf, hpool⟩ := hP
  have hS := hpool.1 N (by omega)
  have hT := hpool.1 (N + 1) (by omega)
  rw [slotOf_self, ← h57] at hS
  rw [slotOf_succ, ← h61] at hT
  have hdisNT := hpool.2.2 N (by omega) (N + 1) (by omega) (by omega)
  have hbN := hpool.2.1 N (by omega)
  have hbT := hpool.2.1 (N + 1) (by omega)
  obtain ⟨s', t, hx, hW', hregs, hF, h54a, h54b, hm⟩ :=
    mergeProg_spec (w := w) (D := N + M + 1) hS hT hdisNT.1 hbN.2.1 h54 h54M
      (fun a ha => by rw [hc.blockLen ha]; exact h54M) h35 hc.2.2.1 (by omega) (by omega)
  have hregs' : ∀ r : ℕ, r ≠ 35 → r ≠ 54 → r ≠ 57 → (r < 62 ∨ 74 < r) → s'.regs r = s.regs r := by
    intro r h1 h2 h3 h4
    exact hregs r fun hr => by have := mergeProg_regs r hr; omega
  have hW50 : ∀ a q, MergeCells (s.regs 57) (s.regs 54) (nsOf N ++ nsOf (N + 1)) a q → 50 ≤ a := by
    intro a q h
    simp only [MergeCells, IsBlockArr, Field.array] at h
    omega
  have hc' : Common N M s₀ s' := hc.step hF hW50 hW' fun r hr => hregs' r (by omega) (by omega)
    (by omega) (by omega)
  refine ⟨s', t, hx, hc', hregs', h54a, h54b, ?_⟩
  cases hmc : merge cur child with
  | none =>
    rw [hmc] at hm
    exact hm
  | some m =>
    rw [hmc] at hm
    obtain ⟨h35', h57', bs', ns', hO, hperm, hbs, ht⟩ := hm
    refine ⟨h35', ?_, ?_⟩
    · -- The new pool.
      have h53' : s'.regs 53 = s.regs 53 := hregs' 53 (by decide) (by decide) (by decide) (by omega)
      have h55' : s'.regs 55 = s.regs 55 := hregs' 55 (by decide) (by decide) (by decide) (by omega)
      have h62 : s'.arrs Field.result.array = s.arrs Field.result.array :=
        hF.arr_eq fun q h => by simp [MergeCells, IsBlockArr, Field.array] at h
      refine ⟨Function.update (Function.update ptr N (s'.regs 57)) (N + 1) 0, ⟨Function.update
        (Function.update bsOf N bs') (N + 1) [], Function.update (Function.update nsOf N ns')
        (N + 1) [], ?_⟩, by simp, by simp, ?_⟩
      · refine PoolAt.update (fun v => v = N ∨ v = N + 1) hpool hF (by omega) h54a (by omega)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro v hv hT'
          push Not at hT'
          have hvN : v < N := by omega
          simp [slotOf_lt hvN, Function.update_of_ne hT'.1, Function.update_of_ne hT'.2]
        · intro v hv hT'
          push Not at hT'
          have hd := hpool.2.2 v hv N (by omega) hT'.1
          have hd' := hpool.2.2 v hv (N + 1) (by omega) hT'.2
          have hbv := hpool.2.1 v hv
          refine ⟨fun hp h => ?_, fun q hq h => ?_, fun q hq h => ?_⟩
          · simp only [SummaryCell, MergeCells, IsBlockArr, Field.array] at h
            have : ptr v = s.regs 57 := by omega
            exact hd.2.2 hp (this.trans h57)
          · simp only [BlockCell, MergeCells, IsBlockArr, Field.array] at h
            have := hbv.2.1 q hq
            omega
          · simp [NodeCell, MergeCells, IsBlockArr, Field.array] at h
            rcases h with hq' | hq'
            · exact hd.1 q hq hq'
            · exact hd'.1 q hq hq'
        · intro v hv hT'
          rcases hT' with rfl | rfl
          · simp only [Function.update_of_ne (show v ≠ v + 1 by omega), Function.update_self,
              slotOf_self]
            refine ⟨hO, fun q hq => ?_, fun q hq => ?_, ?_⟩
            · have := hperm.subset hq
              rcases List.mem_append.mp this with h | h
              · have := hbN.1 q h; omega
              · have := hbT.1 q h; omega
            · rcases hbs q hq with h | h | h
              · have := hbN.2.1 q h; omega
              · have := hbT.2.1 q h; omega
              · omega
            · rcases h57' with h | h <;> rw [h]
              · have := hbN.2.2; omega
              · have := hbT.2.2; omega
          · simp only [Function.update_self, slotOf_succ]
            exact ⟨⟨rfl, rfl, rfl⟩, by simp, by simp, by omega⟩
        · intro v hv hT' q hq
          rcases hT' with rfl | rfl
          · simp only [Function.update_of_ne (show v ≠ v + 1 by omega), Function.update_self] at hq
            rcases List.mem_append.mp (hperm.subset hq) with h | h
            · exact Or.inl ⟨v, hv, Or.inl rfl, h⟩
            · exact Or.inl ⟨v + 1, by omega, Or.inr rfl, h⟩
          · simp at hq
        · intro v hv hT' q hq
          rcases hT' with rfl | rfl
          · simp only [Function.update_of_ne (show v ≠ v + 1 by omega), Function.update_self] at hq
            rcases hbs q hq with h | h | h
            · exact Or.inl ⟨v, hv, Or.inl rfl, h⟩
            · exact Or.inl ⟨v + 1, by omega, Or.inr rfl, h⟩
            · exact Or.inr h.1
          · simp at hq
        · intro v hv hT' hp
          rcases hT' with rfl | rfl
          · simp only [Function.update_of_ne (show v ≠ v + 1 by omega), Function.update_self]
              at hp ⊢
            rcases h57' with h | h
            · exact Or.inl ⟨v, hv, Or.inl rfl, by rw [← h57, ← h]; exact hp, by rw [h, h57]⟩
            · exact Or.inl ⟨v + 1, by omega, Or.inr rfl, by rw [← h61, ← h]; exact hp,
                by rw [h, h61]⟩
          · simp at hp
        · intro u hu v hv hTu hTv huv
          rcases hTu with hu' | hu' <;> rcases hTv with hv' | hv' <;> subst u v
          · exact absurd rfl huv
          · simp
          · simp
          · exact absurd rfl huv
      · intro v hv
        rw [Function.update_of_ne (show v ≠ N + 1 by omega),
          Function.update_of_ne (show v ≠ N by omega), h62]
        exact hR v hv
    · -- The cost.
      have hnS := hS.nodes_length
      have hnT := hT.nodes_length
      have hnO := hO.nodes_length
      have hlen := hperm.length_eq
      simp only [List.length_append] at hlen
      rw [weight_eq, weight_eq, weight_eq]
      omega

/-! ### The round -/

theorem binop_mul {w a b : ℕ} (h : a * b < 2 ^ w) : BinOp.eval w .mul a b = some (a * b) := by
  simp [BinOp.eval, BinOp.raw, checkWord_of_lt h]

theorem Common.setReg {N M : ℕ} {s₀ s : State} (h : Common N M s₀ s) {r : ℕ}
    (hr : r = 35 ∨ 52 ≤ r) (x : ℕ) : Common N M s₀ (s.setReg r x) :=
  ⟨h.1, fun r' hr' => by
    have : r' ≠ r := by omega
    simp [this, h.2.1 r' hr'], h.2.2.1, h.2.2.2⟩

theorem RepAt.setReg {s : State} {N M : ℕ} {results : Array (Option Summary)}
    {cur : Option Summary} {p : ℕ} (h : RepAt s N M results cur p) {r : ℕ}
    (hr : r ≠ 53 ∧ r ≠ 54 ∧ r ≠ 55) (x : ℕ) : RepAt (s.setReg r x) N M results cur p := by
  obtain ⟨ptr, hP, h1, h2, h3⟩ := h
  exact ⟨ptr, hP.congr rfl (by simp [Ne.symm hr.1]) (by simp [Ne.symm hr.2.1])
    (by simp [Ne.symm hr.2.2]), h1, h2, h3⟩

theorem OutgoingChain.cons_inv {s : State} {q i : ℕ} {es : List ℕ}
    (h : OutgoingChain s q (i :: es)) :
    q = i + 1 ∧ ∃ q', (s.arrs Field.outgoingNext.array)[i]? = some q' ∧ OutgoingChain s q' es := by
  cases h with
  | cons hn ht => exact ⟨rfl, _, hn, ht⟩

/-- The test of the edge loop: the flag times the pointer to the remaining
edges. It is zero after a rejection or at the end of the list. -/
def edgeCond : Expr := .op .mul (.reg 35) (.reg 58)

/-- One round of the edge loop. -/
def edgeBodyProg : Cmd :=
  .seq (.assign 59 (.op .sub (.reg 58) (.const 1)))
  (.seq (.assign 60 (.read Field.head.array (.reg 59)))
  (.seq (.assign 73 (.read Field.tree.array (.reg 59)))
  (.seq childProg
  (.seq mergeProg
    (.assign 58 (.read Field.outgoingNext.array (.reg 59)))))))

/-- The edge loop of one vertex. -/
def edgeLoopProg : Cmd := .while edgeCond edgeBodyProg

/-- The state of the edge loop between two rounds. The remaining edges are
`es`, the stored summaries `results`, and the current summary `cur`. Each
remaining edge, and each of the `R` edges of later vertices, may still take
one return node, one block and one summary record. -/
structure EdgeState (N M : ℕ) (search : Search) (s₀ : State) (R k v : ℕ) (es : List ℕ)
    (results : Array (Option Summary)) (cur : Option Summary) (s : State) : Prop where
  common : Common N M s₀ s
  flag : s.regs 35 = 1
  r52 : s.regs 52 = k
  r56 : s.regs 56 = v
  chain : OutgoingChain s (s.regs 58) es
  edges : ∀ i ∈ es, i < search.edges.size
  size : results.size = N
  rep : RepAt s N M results cur (s.regs 57)
  pos53 : 0 < s.regs 53
  pos54 : 0 < s.regs 54
  pos55 : 0 < s.regs 55
  budget53 : s.regs 53 + es.length + R ≤ M + 1
  budget54 : s.regs 54 + es.length + R ≤ M + 1
  budget55 : s.regs 55 + es.length + R ≤ M + 1

/-- The state after a rejected merge. -/
structure EdgeStop (N M : ℕ) (s₀ : State) (k v : ℕ) (s : State) : Prop where
  common : Common N M s₀ s
  flag : s.regs 35 = 0
  r52 : s.regs 52 = k
  r56 : s.regs 56 = v
  r58 : s.regs 58 ≤ M

/-- The invariant of the edge loop. The ghost is `none` after a rejection,
and otherwise holds the remaining edges and summaries. Either way it agrees
with the final value `res` of `solveOutgoing`. -/
def EdgeInv (N M : ℕ) (search : Search) (s₀ : State) (R k v : ℕ)
    (res : Option (Array (Option Summary) × Option Summary)) :
    Option (List ℕ × Array (Option Summary) × Option Summary) → State → Prop
  | none, s => EdgeStop N M s₀ k v s ∧ res = none
  | some (es, results, cur), s => EdgeState N M search s₀ R k v es results cur s ∧
      solveOutgoing search es results cur = res

/-- The potential of the edge loop: 500 per remaining edge plus the weights of
the live summaries. -/
def edgePot : Option (List ℕ × Array (Option Summary) × Option Summary) → ℕ
  | none => 0
  | some (es, results, cur) => 500 * es.length + arraySum weight results + weight cur

theorem edgeRound {N M w : ℕ} {search : Search} {s₀ : State} (hin : SolveInput N M w search s₀)
    {R k v : ℕ} {res : Option (Array (Option Summary) × Option Summary)} :
    ∀ g s, EdgeInv N M search s₀ R k v res g s → ∃ c, edgeCond.eval w s = some c ∧ (c ≠ 0 →
      ∃ g' s' t, Exec w edgeBodyProg s s' t ∧ EdgeInv N M search s₀ R k v res g' s' ∧
        edgeCond.cost + t + edgePot g' ≤ edgePot g) := by
  have hw := hin.word
  have hE := hin.edges_le
  intro g s hI
  match g, hI with
  | none, ⟨hst, _⟩ =>
    refine ⟨0, ?_, fun h => absurd rfl h⟩
    rw [edgeCond, eval_op (eval_reg (by rw [hst.flag]; omega)) (eval_reg (by have := hst.r58; omega)),
      binop_mul (by rw [hst.flag]; omega), hst.flag, Nat.zero_mul]
  | some (es, results, cur), ⟨hst, hres⟩ =>
  have h58 : s.regs 58 ≤ search.edges.size := hst.chain.ptr_le hst.edges
  refine ⟨s.regs 58, ?_, fun hc0 => ?_⟩
  · rw [edgeCond, eval_op (eval_reg (by rw [hst.flag]; omega)) (eval_reg (by omega)),
      binop_mul (by rw [hst.flag]; omega), hst.flag, Nat.one_mul]
  cases es with
  | nil =>
    have hch := hst.chain
    generalize s.regs 58 = q at hch hc0
    cases hch
    exact absurd rfl hc0
  | cons i es =>
  obtain ⟨hq, q', hnext, hchain'⟩ := hst.chain.cons_inv
  have hi : i < search.edges.size := hst.edges i List.mem_cons_self
  have hes : ∀ j ∈ es, j < search.edges.size := fun j hj => hst.edges j (List.mem_cons_of_mem _ hj)
  have hq' : q' ≤ search.edges.size := hchain'.ptr_le hes
  have hc := hst.common
  have hb53 := hst.budget53
  have hb54 := hst.budget54
  have hb55 := hst.budget55
  simp only [List.length_cons] at hb53 hb54 hb55
  obtain ⟨ptr, hP, hpN, hp1, hR⟩ := hst.rep
  set target := search.edges[i]!.target with htdef
  have ht : target < N := (hin.edge hi).2.1
  -- Read the edge record.
  let s₁ := s.setReg 59 i
  have hx₁ : Exec w (.assign 59 (.op .sub (.reg 58) (.const 1))) s s₁ 4 := by
    have := exec_subc (w := w) (s := s) (dst := 59) (r := 58) (by omega) (by omega)
    rwa [hq, Nat.add_sub_cancel] at this
  let s₂ := s₁.setReg 60 target
  have hx₂ : Exec w (.assign 60 (.read Field.head.array (.reg 59))) s₁ s₂ 3 :=
    exec_ld (by simp [s₁]; omega) (by simpa [s₁] using head_read hin hc hi) (by omega)
  let s₃ := s₂.setReg 73 search.edges[i]!.tree.toNat
  have hx₃ : Exec w (.assign 73 (.read Field.tree.array (.reg 59))) s₂ s₃ 3 :=
    exec_ld (by simp [s₂, s₁]; omega) (by simpa [s₂, s₁] using tree_read hin hc hi)
      (by have : search.edges[i]!.tree.toNat ≤ 1 := Bool.toNat_le _; omega)
  have hc₃ : Common N M s₀ s₃ := ((hc.setReg (by omega) _).setReg (by omega) _).setReg (by omega) _
  have hP₃ : PoolOf s₃ N M results cur none ptr := hP.congr rfl (by simp [s₃, s₂, s₁])
    (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂, s₁])
  have hr₃ : ∀ r : ℕ, r ≠ 59 → r ≠ 60 → r ≠ 73 → s₃.regs r = s.regs r := by
    intro r h1 h2 h3; simp [s₃, s₂, s₁, h1, h2, h3]
  -- The child.
  have h53₃ : s₃.regs 53 = s.regs 53 := hr₃ 53 (by decide) (by decide) (by decide)
  have h55₃ : s₃.regs 55 = s.regs 55 := hr₃ 55 (by decide) (by decide) (by decide)
  have hpos53 := hst.pos53
  have hpos55 := hst.pos55
  obtain ⟨s₄, t₄, ptr₄, hx₄, ht₄, hc₄, hP₄, hR₄, hpN₄, h61₄, hr₄, h53a, h53b, h55a, h55b, hwt,
      hsz₄⟩ := childProg_spec hin hc₃ hP₃ hR hst.size (i := i) (by simp [s₃, s₂, s₁]) hi
      (by simp [s₃, s₂]; exact htdef) (by simp [s₃]) (by omega) (by omega) (by omega) (by omega)
  have e4 : ∀ r : ℕ, r ≠ 53 → r ≠ 55 → r ≠ 61 → r ≠ 72 → r ≠ 59 → r ≠ 60 → r ≠ 73 →
      s₄.regs r = s.regs r := fun r a b c d e f g => (hr₄ r a b c d).trans (hr₃ r e f g)
  rw [h53₃] at h53a h53b
  rw [h55₃] at h55a h55b
  -- The merge.
  have h54₄ : s₄.regs 54 = s.regs 54 := e4 54 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h57₄ : s₄.regs 57 = ptr₄ N := by
    rw [e4 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hpN₄, hpN]
  have h35₄ : s₄.regs 35 = 1 := by
    rw [e4 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    exact hst.flag
  have hpos54 := hst.pos54
  obtain ⟨s₅, t₅, hx₅, hc₅, hr₅, h54a, h54b, hm⟩ := mergeStep hin hc₄ hP₄ hR₄ h57₄ h61₄ h35₄
    (by omega) (by omega) (by omega)
  rw [h54₄] at h54a h54b
  have e5 : ∀ r : ℕ, r = 52 ∨ r = 56 → s₅.regs r = s.regs r := by
    intro r hr
    rw [hr₅ r (by omega) (by omega) (by omega) (by omega)]
    exact e4 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h59₅ : s₅.regs 59 = i := by
    rw [hr₅ 59 (by decide) (by decide) (by decide) (by omega),
      hr₄ 59 (by decide) (by decide) (by decide) (by decide)]
    simp [s₃, s₂, s₁]
  -- The next edge.
  have h49 : s₅.arrs Field.outgoingNext.array = s.arrs Field.outgoingNext.array :=
    (hc₅.1 _ (by simp [Field.array])).trans (hc.1 _ (by simp [Field.array])).symm
  let s₆ := s₅.setReg 58 q'
  have hx₆ : Exec w (.assign 58 (.read Field.outgoingNext.array (.reg 59))) s₅ s₆ 3 :=
    exec_ld (by omega) (by rw [h59₅, h49]; exact hnext) (by omega)
  have hx : Exec w edgeBodyProg s s₆ (4 + (3 + (3 + (t₄ + (t₅ + 3))))) :=
    Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅ hx₆))))
  have hc₆ : Common N M s₀ s₆ := hc₅.setReg (by omega) _
  have g52 : s₆.regs 52 = k := by
    rw [show s₆.regs 52 = s₅.regs 52 by simp [s₆], e5 52 (by omega)]; exact hst.r52
  have g56 : s₆.regs 56 = v := by
    rw [show s₆.regs 56 = s₅.regs 56 by simp [s₆], e5 56 (by omega)]; exact hst.r56
  have g58 : s₆.regs 58 = q' := by simp [s₆]
  have g35 : s₆.regs 35 = s₅.regs 35 := by simp [s₆]
  have hcost : edgeCond.cost = 3 := rfl
  rw [solveOutgoing_cons] at hres
  cases hmc : merge cur (edgeChild search i results) with
  | none =>
    rw [hmc] at hm hres
    refine ⟨none, s₆, _, hx, ⟨⟨hc₆, by rw [g35]; exact hm.1, g52, g56, by omega⟩, hres.symm⟩, ?_⟩
    have := hm.2
    have h1 := weight_eq cur
    have h2 := weight_eq (edgeChild search i results)
    simp only [edgePot, List.length_cons, hcost]
    omega
  | some m =>
    rw [hmc] at hm hres
    simp only [Option.bind] at hres
    obtain ⟨h35₅, hrep₅, hcm⟩ := hm
    have g53 : s₆.regs 53 = s₄.regs 53 := by
      rw [show s₆.regs 53 = s₅.regs 53 by simp [s₆]]
      exact hr₅ 53 (by decide) (by decide) (by decide) (by omega)
    have g54 : s₆.regs 54 = s₅.regs 54 := by simp [s₆]
    have g55 : s₆.regs 55 = s₄.regs 55 := by
      rw [show s₆.regs 55 = s₅.regs 55 by simp [s₆]]
      exact hr₅ 55 (by decide) (by decide) (by decide) (by omega)
    have g57 : s₆.regs 57 = s₅.regs 57 := by simp [s₆]
    refine ⟨some (es, edgeResults search i results, m), s₆, _, hx, ⟨⟨hc₆, by rw [g35]; exact h35₅,
      g52, g56, by rw [g58]; exact hchain'.of_arrs_eq h49, hes, hsz₄,
      by rw [g57]; exact hrep₅.setReg ⟨by decide, by decide, by decide⟩ q', by omega, by omega,
      by omega, by omega, by omega, by omega⟩, hres⟩, ?_⟩
    simp only [edgePot, List.length_cons, hcost]
    omega

/-! ### The edge loop -/

/-- The edge loop of a vertex refines `solveOutgoing` from the empty summary.
After a rejection the flag is zero. Otherwise the loop ends with no
remaining edges, and the potential pays for its time. -/
theorem edgeLoop_spec {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) {R k v : ℕ} {es : List ℕ}
    {results : Array (Option Summary)}
    (hst : EdgeState N M search s₀ R k v es results none s) :
    ∃ s' t, Exec w edgeLoopProg s s' t ∧
      match solveOutgoing search es results none with
      | none => EdgeStop N M s₀ k v s' ∧ t ≤ 500 * es.length + arraySum weight results + 3
      | some (results', cur') => EdgeState N M search s₀ R k v [] results' cur' s' ∧
          t + arraySum weight results' + weight cur' ≤
            500 * es.length + arraySum weight results + 3 := by
  have hw := hin.word
  obtain ⟨g', s', t, hx, hI, hc0, hle⟩ := Exec.while_pot
    (EdgeInv N M search s₀ R k v (solveOutgoing search es results none)) edgePot (edgeRound hin)
    (some (es, results, none)) s ⟨hst, rfl⟩
  have hcost : edgeCond.cost = 3 := rfl
  simp only [edgePot, hcost] at hle
  refine ⟨s', t, hx, ?_⟩
  match g', hI with
  | none, ⟨hstop, hres⟩ =>
    rw [hres]
    exact ⟨hstop, by simp [weight] at hle; omega⟩
  | some (es', results', cur'), ⟨hst', hres⟩ =>
    have h58 : s'.regs 58 ≤ search.edges.size := hst'.chain.ptr_le hst'.edges
    have hE := hin.edges_le
    rw [edgeCond, eval_op (eval_reg (by rw [hst'.flag]; omega)) (eval_reg (by omega)),
      binop_mul (by rw [hst'.flag]; omega), hst'.flag, Nat.one_mul] at hc0
    have h0 : s'.regs 58 = 0 := by simpa using hc0
    have hnil : es' = [] := by
      have hch := hst'.chain
      rw [h0] at hch
      exact hch.eq_nil
    subst hnil
    rw [← hres]
    simp only [solveOutgoing]
    simp only [List.length_nil] at hle
    exact ⟨hst', by simp [weight] at hle ⊢; omega⟩

end GraphMinor.Compute.PlanarityRam
