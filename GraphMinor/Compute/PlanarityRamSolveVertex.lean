module

public import GraphMinor.Compute.PlanarityRamSolveRound
import GraphMinor.Compute.WhileRounds

/-!
# One vertex of the solver

Part I, Section 6 of the planarity note processes the vertices in postorder:

    for v in postorder:
        S := empty
        for each outgoing edge of v: S := MERGE(S, child)
        if v has a parent u: S := TRIM(S, depth(u))
        store S as the summary of v

The edge loop is `edgeLoop_spec`. This file adds the trim and the store
(`finishStep`), proves that one round of the vertex loop refines one step
of `solveFrom` (`vertexRound`), and proves the vertex loop
(`vertexLoop_spec`). The potential of the vertex loop is a constant per
remaining vertex, 500 per remaining outgoing edge, and the weights of the
stored summaries.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-! ### Trim -/

/-- `TRIM` on the current summary, with the depth bound in register 62. -/
theorem trimStep {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s)
    {results : Array (Option Summary)} {cur : Option Summary}
    (hrep : RepAt s N M results cur (s.regs 57)) (hcD : s.regs 62 ≤ N + M + 1) :
    ∃ s' t, Exec w trimProg s s' t ∧ Common N M s₀ s' ∧
      RepAt s' N M results (trim cur (s.regs 62)) (s'.regs 57) ∧
      (∀ r : ℕ, r ≠ 57 → (r < 67 ∨ 74 < r) → s'.regs r = s.regs r) ∧
      t + weight (trim cur (s.regs 62)) ≤ 100 + weight cur := by
  have hw := hin.word
  obtain ⟨ptr, ⟨bsOf, nsOf, hpool⟩, hpN, hp1, hR⟩ := hrep
  have hS := hpool.1 N (by omega)
  rw [slotOf_self, hpN] at hS
  obtain ⟨s', t, bs', ns', hx, hW', hregs, hF, h57', hO, hbs, hns, ht⟩ :=
    trimProg_spec (w := w) (D := N + M + 1) hS hcD hc.2.2.1 (by omega) (by omega)
  have hW50 : ∀ a q, TrimCells (s.regs 57) (bsOf N) a q → 50 ≤ a := by
    intro a q h
    simp only [TrimCells, IsBlockArr, Field.array] at h
    omega
  have hc' : Common N M s₀ s' :=
    hc.step hF hW50 hW' fun r hr => hregs r (by omega) (by omega)
  have h53' : s'.regs 53 = s.regs 53 := hregs 53 (by decide) (by omega)
  have h54' : s'.regs 54 = s.regs 54 := hregs 54 (by decide) (by omega)
  have h55' : s'.regs 55 = s.regs 55 := hregs 55 (by decide) (by omega)
  have h62 : s'.arrs Field.result.array = s.arrs Field.result.array :=
    hF.arr_eq fun q h => by simp [TrimCells, IsBlockArr, Field.array] at h
  refine ⟨s', t, hx, hc', ⟨Function.update ptr N (s'.regs 57), ⟨Function.update bsOf N bs',
    Function.update nsOf N ns', ?_⟩, by simp, by simp [hp1], ?_⟩, hregs, ht⟩
  · have hbN := hpool.2.1 N (by omega)
    refine PoolAt.update (· = N) hpool hF (by omega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro u hu hT
      refine ⟨?_, Function.update_of_ne hT _ _, Function.update_of_ne hT _ _,
        Function.update_of_ne hT _ _⟩
      unfold slotOf
      by_cases h : u < N
      · simp [h]
      · simp [h, hT]
    · intro u hu hT
      have hd := hpool.2.2 u hu N (by omega) hT
      have hbu := hpool.2.1 u hu
      refine ⟨fun hp h => ?_, fun q hq h => ?_, fun q hq h => ?_⟩
      · simp only [SummaryCell, TrimCells, IsBlockArr, Field.array] at h
        have : ptr u = s.regs 57 := by omega
        exact hd.2.2 hp (this.trans hpN.symm)
      · simp [BlockCell, TrimCells, IsBlockArr, Field.array] at h
        exact hd.2.1 q hq h
      · simp [NodeCell, TrimCells, IsBlockArr, Field.array] at h
    · intro u hu hT
      subst u
      simp only [Function.update_self, slotOf_self]
      refine ⟨hO, fun q hq => ?_, fun q hq => ?_, ?_⟩
      · have := hbN.1 q (hns.subset hq); omega
      · have := hbN.2.1 q (hbs.subset hq); omega
      · rcases h57' with h | h <;> rw [h]
        · have := hbN.2.2; omega
        · have := hpool.2.1 N (by omega); omega
    · intro u hu hT q hq
      subst u
      simp only [Function.update_self] at hq
      exact Or.inl ⟨N, hu, rfl, hns.subset hq⟩
    · intro u hu hT q hq
      subst u
      simp only [Function.update_self] at hq
      exact Or.inl ⟨N, hu, rfl, hbs.subset hq⟩
    · intro u hu hT hp
      subst u
      simp only [Function.update_self] at hp ⊢
      rcases h57' with h | h
      · exact Or.inl ⟨N, hu, rfl, by rw [hpN, ← h]; exact hp, by rw [h, hpN]⟩
      · exact absurd h hp
    · intro u _ v _ hTu hTv huv
      exact absurd (hTu.trans hTv.symm) huv
  · intro v hv
    rw [Function.update_of_ne (show v ≠ N by omega), h62]
    exact hR v hv

/-- `c := depth(u)` for the parent `u` in register 72, then `TRIM(S, c)`. -/
def trimArgProg : Cmd :=
  .seq (.assign 72 (.op .sub (.reg 72) (.const 1)))
  (.seq (.assign 62 (.read Field.depth.array (.reg 72)))
  (.seq (.assign 62 (.op .sub (.reg 62) (.const 1))) trimProg))

/-- Read the parent of `v` (register 56) and trim if it has one. -/
def parentTrimProg : Cmd :=
  .seq (.assign 72 (.read Field.parent.array (.reg 56))) (.ite (.reg 72) trimArgProg .skip)

theorem parentTrimStep {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s)
    {results : Array (Option Summary)} {cur : Option Summary}
    (hrep : RepAt s N M results cur (s.regs 57)) {v : ℕ} (h56 : s.regs 56 = v) (hv : v < N) :
    ∃ s' t, Exec w parentTrimProg s s' t ∧ Common N M s₀ s' ∧
      RepAt s' N M results (solveTrim search v cur) (s'.regs 57) ∧
      (∀ r : ℕ, r ≠ 57 → r ≠ 62 → (r < 67 ∨ 74 < r) → s'.regs r = s.regs r) ∧
      t + weight (solveTrim search v cur) ≤ 120 + weight cur := by
  have hw := hin.word
  have hparent := parent_read hin hc hv
  let s₁ := s.setReg 72 (optionWord (search.parent[v]?.join))
  have hc₁ : Common N M s₀ s₁ := hc.setReg (by omega) _
  have hrep₁ : RepAt s₁ N M results cur (s₁.regs 57) := by
    rw [show s₁.regs 57 = s.regs 57 by simp [s₁]]
    exact hrep.setReg ⟨by decide, by decide, by decide⟩ _
  cases hpar : search.parent[v]?.join with
  | none =>
    have hx₁ : Exec w (.assign 72 (.read Field.parent.array (.reg 56))) s s₁ 3 :=
      exec_ld (by omega) (by rw [h56]; exact hparent) (by rw [hpar]; simp only [optionWord]; omega)
    have hx := Exec.seq hx₁ (exec_ite_zero (w := w) (c₁ := trimArgProg) (s := s₁) (r := 72)
      (by simp [s₁, hpar, optionWord]) (Exec.skip s₁))
    refine ⟨s₁, _, hx, hc₁, by simpa [solveTrim, hpar] using hrep₁, fun r h1 h2 h3 => ?_, ?_⟩
    · simp [s₁, show r ≠ 72 by omega]
    · simp [solveTrim, hpar]
  | some u =>
    have hu : u < N := hin.bounded.2.2.2.2.1 ⟨v, hv⟩ u hpar
    have hx₁ : Exec w (.assign 72 (.read Field.parent.array (.reg 56))) s s₁ 3 :=
      exec_ld (by omega) (by rw [h56]; exact hparent) (by simp [hpar, optionWord]; omega)
    have h72 : s₁.regs 72 = u + 1 := by simp [s₁, hpar, optionWord]
    let s₂ := s₁.setReg 72 u
    have hx₂ : Exec w (.assign 72 (.op .sub (.reg 72) (.const 1))) s₁ s₂ 4 := by
      have := exec_subc (w := w) (s := s₁) (dst := 72) (r := 72) (by omega) (by omega)
      rwa [h72, Nat.add_sub_cancel] at this
    set o := search.depth[u]?.join with hodef
    have hoN : o.getD 0 < N ∨ o = none := by
      cases ho : o with
      | none => exact Or.inr rfl
      | some d => exact Or.inl (by simpa using hin.bounded.2.2.2.1 ⟨u, hu⟩ d (by rw [← ho]))
    have hword : optionWord o ≤ N := by
      cases ho : o with
      | none => simp [optionWord]
      | some d => rw [ho] at hoN; simp [optionWord] at hoN ⊢; omega
    let s₃ := s₂.setReg 62 (optionWord o)
    have hx₃ : Exec w (.assign 62 (.read Field.depth.array (.reg 72))) s₂ s₃ 3 :=
      exec_ld (by simp [s₂]; omega) (by simpa [s₂, s₁] using depth_read hin hc hu) (by omega)
    let s₄ := s₃.setReg 62 (o.getD 0)
    have hx₄ : Exec w (.assign 62 (.op .sub (.reg 62) (.const 1))) s₃ s₄ 4 := by
      have := exec_subc (w := w) (s := s₃) (dst := 62) (r := 62) (by simp [s₃]; omega) (by omega)
      simpa [s₄, s₃, optionWord_sub_one] using this
    have hc₄ : Common N M s₀ s₄ := ((hc₁.setReg (by omega) _).setReg (by omega) _).setReg
      (by omega) _
    have hrep₄ : RepAt s₄ N M results cur (s₄.regs 57) := by
      rw [show s₄.regs 57 = s₁.regs 57 by simp [s₄, s₃, s₂]]
      exact ((hrep₁.setReg ⟨by decide, by decide, by decide⟩ _).setReg
        ⟨by decide, by decide, by decide⟩ _).setReg ⟨by decide, by decide, by decide⟩ _
    have h62 : s₄.regs 62 = o.getD 0 := by simp [s₄]
    have hcD : o.getD 0 ≤ N + M + 1 := by
      rcases hoN with h | h
      · omega
      · simp [h]
    obtain ⟨s₅, t₅, hx₅, hc₅, hrep₅, hr₅, ht₅⟩ := trimStep hin hc₄ hrep₄ (by rw [h62]; exact hcD)
    rw [h62] at hrep₅ ht₅
    have hx := Exec.seq hx₁ (exec_ite_pos (c₂ := .skip) (s := s₁) (r := 72) (by rw [h72]; omega)
      (by rw [h72]; omega)
      (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ hx₅))))
    have htrim : solveTrim search v cur = trim cur (o.getD 0) := by simp [solveTrim, hpar, hodef]
    refine ⟨s₅, _, hx, hc₅, by rw [htrim]; exact hrep₅, fun r h1 h2 h3 => ?_, by rw [htrim]; omega⟩
    rw [hr₅ r h1 h3]
    simp [s₄, s₃, s₂, s₁, h2, show r ≠ 72 by omega]

/-! ### Store -/

/-- `result[v] := S` and move on to the next vertex. -/
def storeProg : Cmd :=
  .seq (.write Field.result.array (.reg 56) (.reg 57)) (.assign 52 (.op .add (.reg 52) (.const 1)))

theorem storeStep {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s)
    {results : Array (Option Summary)} {cur : Option Summary}
    (hrep : RepAt s N M results cur (s.regs 57)) (hsz : results.size = N) {v : ℕ}
    (h56 : s.regs 56 = v) (hv : v < N) (h52 : s.regs 52 + 1 < 2 ^ w) :
    ∃ s', Exec w storeProg s s' 7 ∧ Common N M s₀ s' ∧ RepAt s' N M (results.set! v cur) none 0 ∧
      s'.regs 52 = s.regs 52 + 1 ∧ (∀ r : ℕ, r ≠ 52 → s'.regs r = s.regs r) := by
  have hw := hin.word
  obtain ⟨ptr, ⟨bsOf, nsOf, hpool⟩, hpN, hp1, hR⟩ := hrep
  have hbN := hpool.2.1 N (by omega)
  have hlen : (s.arrs Field.result.array).length = N := by
    have := hc.2.2.2 Field.result (by simp [solverFields]); simpa [Field.capacity] using this
  have hlen62 : (s.arrs 62).length = N := hlen
  have hpM : ptr N < M + 1 := by
    have h := hpool.1 N (by omega)
    exact h.ptr_lt
  let s₁ := s.writeArr Field.result.array v (s.regs 57)
  let s₂ := s₁.setReg 52 (s.regs 52 + 1)
  have hx : Exec w storeProg s s₂ 7 := by
    have e1 : Exec w (.write Field.result.array (.reg 56) (.reg 57)) s s₁ 3 :=
      exec_st' (w := w) (idx := 56) (val := 57) h56 rfl (by omega) (by omega) (by omega)
    have e2 := exec_addc (w := w) (s := s₁) (r := 52) (by simp [s₁]; omega)
    simp only [s₁, State.writeArr_regs] at e2
    exact Exec.seq e1 e2
  let W : ℕ → ℕ → Prop := fun a q => a = Field.result.array ∧ q = v
  have hF : Frame s s₂ W := (Frame.writeArr s _ _ _).mono fun a q h => by simp [W, h.1, h.2]
  have hc₂ : Common N M s₀ s₂ := (hc.step (s' := s₁) (Frame.writeArr s _ _ _)
    (fun a q h => by simp [Field.array] at h; omega) (hc.2.2.1.writeArr _ _ (by omega))
    (fun r _ => by simp [s₁])).setReg (by omega) _
  refine ⟨s₂, hx, hc₂, ⟨Function.update (Function.update ptr v (ptr N)) N 0,
    ⟨Function.update (Function.update bsOf v (bsOf N)) N [],
      Function.update (Function.update nsOf v (nsOf N)) N [], ?_⟩, by simp,
      by simp [Function.update_of_ne (show N + 1 ≠ v by omega), hp1], ?_⟩,
    by simp [s₂], fun r hr => by simp [s₂, s₁, hr]⟩
  · have hsl : ∀ u < N + 2, slotOf N (results.set! v cur) none none u =
        if u = v then cur else if u = N then none else slotOf N results cur none u := by
      intro u hu
      unfold slotOf
      rw [getElem!_set! _ _ _ _ (by omega)]
      by_cases h1 : u = v
      · simp [h1, hv]
      · by_cases h2 : u < N
        · simp [h1, h2, show u ≠ N by omega]
        · by_cases h3 : u = N
          · simp [h3, show N ≠ v by omega]
          · simp [h1, h2, h3]
    refine PoolAt.update (fun u => u = v ∨ u = N) hpool hF (by simp [s₂, s₁])
      (by simp [s₂, s₁]) (by simp [s₂, s₁]) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro u hu hT
      push Not at hT
      rw [hsl u hu]
      simp [hT.1, hT.2, Function.update_of_ne]
    · intro u hu hT
      refine ⟨fun _ h => ?_, fun q _ h => ?_, fun q _ h => ?_⟩ <;>
        simp [SummaryCell, BlockCell, NodeCell, W, Field.array] at h
    · intro u hu hT
      rcases hT with rfl | rfl
      · simp only [Function.update_of_ne (show u ≠ N by omega), Function.update_self, hsl _ hu,
          ↓reduceIte]
        refine ⟨?_, fun q hq => ?_, fun q hq => ?_, ?_⟩
        · have h := hpool.1 N (by omega)
          rw [slotOf_self] at h
          exact h.frame hF (fun _ h => by simp [SummaryCell, W, Field.array] at h)
            (fun _ _ h => by simp [BlockCell, W, Field.array] at h)
            (fun _ _ h => by simp [NodeCell, W, Field.array] at h)
        · have := hbN.1 q hq; simp [s₂, s₁]; omega
        · have := hbN.2.1 q hq; simp [s₂, s₁]; omega
        · have := hbN.2.2; simp [s₂, s₁]; omega
      · simp only [Function.update_self, hsl _ hu, show u ≠ v by omega, ↓reduceIte]
        refine ⟨⟨rfl, rfl, rfl⟩, by simp, by simp, ?_⟩
        have := hbN.2.2; simp [s₂, s₁]; omega
    · intro u hu hT q hq
      rcases hT with rfl | rfl
      · simp only [Function.update_of_ne (show u ≠ N by omega), Function.update_self] at hq
        exact Or.inl ⟨N, by omega, Or.inr rfl, hq⟩
      · simp at hq
    · intro u hu hT q hq
      rcases hT with rfl | rfl
      · simp only [Function.update_of_ne (show u ≠ N by omega), Function.update_self] at hq
        exact Or.inl ⟨N, by omega, Or.inr rfl, hq⟩
      · simp at hq
    · intro u hu hT hp
      rcases hT with rfl | rfl
      · simp only [Function.update_of_ne (show u ≠ N by omega), Function.update_self] at hp ⊢
        exact Or.inl ⟨N, by omega, Or.inr rfl, hp, rfl⟩
      · simp at hp
    · intro a ha b hb hTa hTb hab
      rcases hTa with ha' | ha' <;> rcases hTb with hb' | hb' <;> subst a b
      · exact absurd rfl hab
      · simp
      · simp only [Function.update_self, Function.update_of_ne (show v ≠ N by omega)]
        simp
      · exact absurd rfl hab
  · intro u hu
    simp only [s₂, s₁]
    by_cases h : u = v
    · subst h
      simp [State.writeArr, State.setArr, hlen62, hu, Field.array, Function.update_of_ne
        (show u ≠ N by omega), hpN]
    · rw [Function.update_of_ne (show u ≠ N by omega), Function.update_of_ne h]
      have := hR u hu
      simp [State.writeArr, State.setArr, Field.array, Ne.symm h] at this ⊢
      exact this

/-! ### The vertex loop -/

/-- Trim and store the summary of the current vertex. -/
def finishProg : Cmd := .seq parentTrimProg storeProg

/-- One round of the vertex loop: `v := postorder[k]`, `S := empty`, the edge
loop, and, unless a merge was rejected, trim and store. -/
def vertexBodyProg : Cmd :=
  .seq (.assign 56 (.read Field.postorder.array (.reg 52)))
  (.seq (.assign 57 (.const 0))
  (.seq (.assign 58 (.read Field.outgoingFirst.array (.reg 56)))
  (.seq edgeLoopProg
    (.ite (.reg 35) finishProg .skip))))

/-- The test of the vertex loop: no rejection and vertices remain. -/
def vertexCond : Expr := .op .mul (.reg 35) (.op .lt (.reg 52) (.reg 39))

/-- The vertex loop. -/
def vertexLoopProg : Cmd := .while vertexCond vertexBodyProg

/-- The number of outgoing edges of the vertices from position `k` of the
postorder on. -/
def restEdges (search : Search) (outgoing : Array (List ℕ)) (k : ℕ) : ℕ :=
  ((search.postorder.drop k).map fun u => (outgoing[u]!).length).sum

/-- The potential of the vertices from position `k` of the postorder on:
200 per vertex and 500 per outgoing edge. -/
def restPot (search : Search) (outgoing : Array (List ℕ)) (k : ℕ) : ℕ :=
  ((search.postorder.drop k).map fun u => 200 + 500 * (outgoing[u]!).length).sum

theorem restEdges_cons (search : Search) (outgoing : Array (List ℕ)) {k : ℕ}
    (hk : k < search.postorder.length) :
    restEdges search outgoing k =
      (outgoing[search.postorder[k]]!).length + restEdges search outgoing (k + 1) := by
  simp only [restEdges, List.drop_eq_getElem_cons hk, List.map_cons, List.sum_cons]

theorem restPot_cons (search : Search) (outgoing : Array (List ℕ)) {k : ℕ}
    (hk : k < search.postorder.length) :
    restPot search outgoing k =
      200 + 500 * (outgoing[search.postorder[k]]!).length + restPot search outgoing (k + 1) := by
  simp only [restPot, List.drop_eq_getElem_cons hk, List.map_cons, List.sum_cons]

/-- The state of the vertex loop before position `k` of the postorder. -/
structure VertexState (N M : ℕ) (search : Search) (s₀ : State) (k : ℕ)
    (results : Array (Option Summary)) (s : State) : Prop where
  common : Common N M s₀ s
  flag : s.regs 35 = 1
  r52 : s.regs 52 = k
  hk : k ≤ search.postorder.length
  size : results.size = N
  rep : RepAt s N M results none 0
  pos53 : 0 < s.regs 53
  pos54 : 0 < s.regs 54
  pos55 : 0 < s.regs 55
  budget53 : s.regs 53 + restEdges search (bucketOrder N search.edges) k ≤ M + 1
  budget54 : s.regs 54 + restEdges search (bucketOrder N search.edges) k ≤ M + 1
  budget55 : s.regs 55 + restEdges search (bucketOrder N search.edges) k ≤ M + 1

/-- The invariant of the vertex loop. The ghost is `none` after a rejection,
and otherwise the position in the postorder and the stored summaries. -/
def VertexInv (N M : ℕ) (search : Search) (s₀ : State) :
    Option (ℕ × Array (Option Summary)) → State → Prop
  | none, s => (Common N M s₀ s ∧ s.regs 35 = 0 ∧ s.regs 52 ≤ search.postorder.length) ∧
      solve N search (bucketOrder N search.edges) = false
  | some (k, results), s => VertexState N M search s₀ k results s ∧
      solveFrom search (bucketOrder N search.edges) (search.postorder.drop k) results =
        solve N search (bucketOrder N search.edges)

/-- The potential of the vertex loop. -/
def vertexPot (N : ℕ) (search : Search) : Option (ℕ × Array (Option Summary)) → ℕ
  | none => 0
  | some (k, results) => restPot search (bucketOrder N search.edges) k + arraySum weight results

theorem vertexCond_eval {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hc : Common N M s₀ s) (h35 : s.regs 35 ≤ 1)
    (h52 : s.regs 52 ≤ search.postorder.length) :
    vertexCond.eval w s =
      some (s.regs 35 * if s.regs 52 < search.postorder.length then 1 else 0) := by
  have hw := hin.word
  have hlen : search.postorder.length ≤ N := hin.searchAt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h39 : s.regs 39 = search.postorder.length := by
    rw [hc.2.1 39 (by omega)]; exact hin.searchAt.2.2.2.2.1
  rw [vertexCond, eval_op (eval_reg (by omega))
    ((eval_op (eval_reg (by omega)) (eval_reg (by omega))).trans (binop_lt (by omega))),
    h39, binop_mul (by split <;> simp <;> omega)]

theorem vertexRound {N M w : ℕ} {search : Search} {s₀ : State}
    (hin : SolveInput N M w search s₀) (hpo : ∀ v ∈ search.postorder, v < N) :
    ∀ g s, VertexInv N M search s₀ g s → ∃ c, vertexCond.eval w s = some c ∧ (c ≠ 0 →
      ∃ g' s' t, Exec w vertexBodyProg s s' t ∧ VertexInv N M search s₀ g' s' ∧
        vertexCond.cost + t + vertexPot N search g' ≤ vertexPot N search g) := by
  have hw := hin.word
  intro g s hI
  match g, hI with
  | none, ⟨⟨hc, h35, h52⟩, _⟩ =>
    refine ⟨0, ?_, fun h => absurd rfl h⟩
    rw [vertexCond_eval hin hc (by omega) h52, h35, Nat.zero_mul]
  | some (k, results), ⟨hst, hsolve⟩ =>
  have hc := hst.common
  refine ⟨_, vertexCond_eval hin hc (le_of_eq hst.flag) (by rw [hst.r52]; exact hst.hk),
    fun hc0 => ?_⟩
  rw [hst.flag, hst.r52, Nat.one_mul] at hc0
  have hk : k < search.postorder.length := by
    by_contra h
    simp [h] at hc0
  obtain ⟨hosz, -, hoedges⟩ := bucketOrder_facts N search.edges
  set v := search.postorder[k] with hvdef
  have hv : v < N := hpo v (List.getElem_mem hk)
  have hE := hin.edges_le
  have hlen : search.postorder.length ≤ N := hin.searchAt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- Start the vertex.
  let s₁ := s.setReg 56 v
  have hx₁ : Exec w (.assign 56 (.read Field.postorder.array (.reg 52))) s s₁ 3 :=
    exec_ld (by rw [hst.r52]; omega) (by rw [hst.r52]; exact postorder_read hin hc hk)
      (by omega)
  let s₂ := s₁.setReg 57 0
  have hx₂ : Exec w (.assign 57 (.const 0)) s₁ s₂ 2 := exec_setc (by omega)
  obtain ⟨first, hfirst, hchain⟩ := hin.outgoing v hv
  have hes : ∀ i ∈ (bucketOrder N search.edges)[v]!, i < search.edges.size := by
    intro i hi
    refine hoedges _ ?_ i hi
    rw [getElem!_pos (bucketOrder N search.edges) v (by omega)]
    exact Array.getElem_mem_toList _
  have hfw : first ≤ search.edges.size := hchain.ptr_le hes
  let s₃ := s₂.setReg 58 first
  have hx₃ : Exec w (.assign 58 (.read Field.outgoingFirst.array (.reg 56))) s₂ s₃ 3 :=
    exec_ld (by simp [s₂, s₁]; omega)
      (by simp only [s₂, s₁, State.setReg_regs_self, State.setReg_regs_ne _ _ (show 56 ≠ 57 by decide)]
          rw [← hc.1 _ (by simp [Field.array])] at hfirst; exact hfirst) (by omega)
  have hc₃ : Common N M s₀ s₃ := ((hc.setReg (by omega) _).setReg (by omega) _).setReg (by omega) _
  have hrc := restEdges_cons search (bucketOrder N search.edges) hk
  rw [← hvdef] at hrc
  have hb53 := hst.budget53
  have hb54 := hst.budget54
  have hb55 := hst.budget55
  have hpos53 := hst.pos53
  have hpos54 := hst.pos54
  have hpos55 := hst.pos55
  have h53₃ : s₃.regs 53 = s.regs 53 := by simp [s₃, s₂, s₁]
  have h54₃ : s₃.regs 54 = s.regs 54 := by simp [s₃, s₂, s₁]
  have h55₃ : s₃.regs 55 = s.regs 55 := by simp [s₃, s₂, s₁]
  have hes₃ : EdgeState N M search s₀ (restEdges search (bucketOrder N search.edges) (k + 1)) k v (bucketOrder N search.edges)[v]!
      results none s₃ := by
    refine ⟨hc₃, by simp [s₃, s₂, s₁, hst.flag], by simp [s₃, s₂, s₁, hst.r52],
      by simp [s₃, s₂, s₁], ?_, hes, hst.size, ?_, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
    · rw [show s₃.regs 58 = first by simp [s₃]]
      exact hchain.of_arrs_eq ((hc₃.1 _ (by simp [Field.array])))
    · rw [show s₃.regs 57 = 0 by simp [s₃, s₂]]
      exact ((hst.rep.setReg ⟨by decide, by decide, by decide⟩ _).setReg
        ⟨by decide, by decide, by decide⟩ _).setReg ⟨by decide, by decide, by decide⟩ _
  -- The edge loop.
  obtain ⟨s₄, t₄, hx₄, hm⟩ := edgeLoop_spec hin hes₃
  have hrp := restPot_cons search (bucketOrder N search.edges) hk
  rw [← hvdef] at hrp
  rw [List.drop_eq_getElem_cons hk, ← hvdef] at hsolve
  simp only [solveFrom] at hsolve
  have hcost : vertexCond.cost = 5 := rfl
  cases hout : solveOutgoing search (bucketOrder N search.edges)[v]! results none with
  | none =>
    rw [hout] at hm hsolve
    obtain ⟨hstop, ht₄⟩ := hm
    have hx := Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄
      (exec_ite_zero (c₁ := finishProg) hstop.flag (Exec.skip s₄)))))
    refine ⟨none, s₄, _, hx, ⟨⟨hstop.common, hstop.flag, by rw [hstop.r52]; omega⟩,
      hsolve.symm⟩, ?_⟩
    simp only [vertexPot, hcost]
    omega
  | some p =>
    obtain ⟨rs, summary⟩ := p
    rw [hout] at hm hsolve
    simp only at hsolve
    obtain ⟨hst₄, ht₄⟩ := hm
    have hc₄ := hst₄.common
    obtain ⟨s₅, t₅, hx₅, hc₅, hrep₅, hr₅, ht₅⟩ :=
      parentTrimStep hin hc₄ hst₄.rep hst₄.r56 hv
    have h52₅ : s₅.regs 52 = k := by rw [hr₅ 52 (by decide) (by decide) (by omega)]; exact hst₄.r52
    have h56₅ : s₅.regs 56 = v := by rw [hr₅ 56 (by decide) (by decide) (by omega)]; exact hst₄.r56
    obtain ⟨s₆, hx₆, hc₆, hrep₆, h52₆, hr₆⟩ :=
      storeStep hin hc₅ hrep₅ hst₄.size h56₅ hv (by omega)
    have hx := Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄
      (exec_ite_pos (c₂ := .skip) (by rw [hst₄.flag]; omega) (by rw [hst₄.flag]; omega)
        (Exec.seq hx₅ hx₆)))))
    have e6 : ∀ r : ℕ, r = 35 ∨ r = 53 ∨ r = 54 ∨ r = 55 → s₆.regs r = s₄.regs r := by
      intro r hr
      rw [hr₆ r (by omega), hr₅ r (by omega) (by omega) (by omega)]
    have hb53' := hst₄.budget53
    have hb54' := hst₄.budget54
    have hb55' := hst₄.budget55
    have hp53 := hst₄.pos53
    have hp54 := hst₄.pos54
    have hp55 := hst₄.pos55
    simp only [List.length_nil, Nat.add_zero] at hb53' hb54' hb55'
    have g53 := e6 53 (by omega)
    have g54 := e6 54 (by omega)
    have g55 := e6 55 (by omega)
    refine ⟨some (k + 1, rs.set! v (solveTrim search v summary)), s₆, _, hx,
      ⟨⟨hc₆, by rw [e6 35 (by omega)]; exact hst₄.flag, by rw [h52₆, h52₅], by omega,
        by simp [hst₄.size], hrep₆, by omega, by omega, by omega, by omega, by omega, by omega⟩,
        hsolve⟩, ?_⟩
    have hset := arraySum_set weight rs v (solveTrim search v summary) (by rw [hst₄.size]; exact hv)
    simp only [vertexPot, hcost]
    omega

/-- The vertex loop computes `solve`. -/
theorem vertexLoop_spec {N M w : ℕ} {search : Search} {s₀ s : State}
    (hin : SolveInput N M w search s₀) (hpo : ∀ v ∈ search.postorder, v < N)
    (hst : VertexState N M search s₀ 0 (Array.replicate N none) s) :
    ∃ s' t, Exec w vertexLoopProg s s' t ∧ Common N M s₀ s' ∧
      s'.regs 35 = (solve N search (bucketOrder N search.edges)).toNat ∧
      t ≤ restPot search (bucketOrder N search.edges) 0 + 5 := by
  have hw := hin.word
  have hsolve : solveFrom search (bucketOrder N search.edges) (search.postorder.drop 0)
      (Array.replicate N none) = solve N search (bucketOrder N search.edges) := by
    rw [List.drop_zero, solve_eq]
  obtain ⟨g', s', t, hx, hI, hc0, hle⟩ := Exec.while_pot (VertexInv N M search s₀)
    (vertexPot N search) (vertexRound hin hpo) (some (0, Array.replicate N none)) s ⟨hst, hsolve⟩
  have hzero : arraySum weight (Array.replicate N (none : Option Summary)) = 0 := by
    simp [arraySum, weight]
  have hcost : vertexCond.cost = 5 := rfl
  simp only [vertexPot, hzero, hcost, Nat.add_zero] at hle
  refine ⟨s', t, hx, ?_⟩
  match g', hI with
  | none, ⟨⟨hc, h35, _⟩, hres⟩ =>
    exact ⟨hc, by rw [h35, hres]; rfl, by omega⟩
  | some (k, results), ⟨hst', hres⟩ =>
    rw [vertexCond_eval hin hst'.common (le_of_eq hst'.flag)
      (by rw [hst'.r52]; exact hst'.hk), hst'.flag, hst'.r52, Nat.one_mul] at hc0
    have hk : k = search.postorder.length := by
      have := hst'.hk
      by_contra h
      simp [show k < search.postorder.length by omega] at hc0
    subst hk
    rw [List.drop_length] at hres
    simp only [solveFrom] at hres
    exact ⟨hst'.common, by rw [hst'.flag, ← hres]; rfl, by omega⟩

end GraphMinor.Compute.PlanarityRam
