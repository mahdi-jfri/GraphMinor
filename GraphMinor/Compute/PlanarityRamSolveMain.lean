module

public import GraphMinor.Compute.PlanarityRamSolveVertex

/-!
# The RAM solver

This file proves `solveRamClaim_proved : PlanarityRamSolveClaim`, the solver
phase of the linear-time planarity test of Part I, Section 6 of the
planarity note.

The program `solveProg` first clears the thirteen solver arenas, so that every
word in them is small, and sets the three bump allocators to one (slot zero is
null). It then runs the vertex loop of `PlanarityRamSolveVertex.lean`.

The time bound is the note's charging argument (Part V, Sections 1 and 2):
the vertex loop pays 200 steps per vertex and 500 per outgoing edge, and the
weights of the summaries pay for the block pops and node moves of `MERGE` and
`TRIM` (`edgeRound`, `vertexRound`). Clearing the arenas costs their total
length.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-! ### Clearing arrays -/

/-- Replace each listed array by zeros of the same length. -/
def zeroProg : List ℕ → Cmd
  | [] => .skip
  | a :: as => .seq (.alloc a (.len a)) (zeroProg as)

theorem zeroProg_spec {w L : ℕ} :
    ∀ (as : List ℕ) (s : State), (∀ a ∈ as, (s.arrs a).length ≤ L) → L < 2 ^ w →
      ∃ s' t, Exec w (zeroProg as) s s' t ∧ t ≤ 1 + as.length * (L + 1) ∧
        s'.regs = s.regs ∧ (∀ a, a ∉ as → s'.arrs a = s.arrs a) ∧
        (∀ a ∈ as, s'.arrs a = List.replicate (s.arrs a).length 0) := by
  intro as
  induction as with
  | nil => intro s _ _; exact ⟨s, 1, Exec.skip s, by simp, rfl, fun _ _ => rfl, by simp⟩
  | cons a as ih =>
    intro s hL hw
    let s₁ := s.setArr a (List.replicate (s.arrs a).length 0)
    have hx₁ : Exec w (.alloc a (.len a)) s s₁ (1 + (s.arrs a).length) := by
      have := Exec.alloc (w := w) (a := a) (len := .len a) (s := s) (m := (s.arrs a).length)
        (by simp [Expr.eval, checkWord]; have := hL a List.mem_cons_self; omega)
      simpa using this
    have hlen₁ : ∀ b, (s₁.arrs b).length = (s.arrs b).length := by
      intro b
      by_cases h : b = a
      · subst h; simp [s₁, State.setArr]
      · simp [s₁, State.setArr, h]
    obtain ⟨s', t, hx, ht, hregs, hkeep, hzero⟩ := ih s₁
      (fun b hb => by rw [hlen₁]; exact hL b (List.mem_cons_of_mem _ hb)) hw
    refine ⟨s', _, Exec.seq hx₁ hx, ?_, by rw [hregs]; rfl, fun b hb => ?_, fun b hb => ?_⟩
    · have := hL a List.mem_cons_self
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · rw [hkeep b (fun h => hb (List.mem_cons_of_mem _ h))]
      have hba : b ≠ a := fun h => hb (h ▸ List.mem_cons_self)
      simp only [s₁, State.setArr]
      exact Function.update_of_ne hba _ _
    · by_cases h : b ∈ as
      · rw [hzero b h, hlen₁]
      · rcases List.mem_cons.mp hb with rfl | h'
        · rw [hkeep b h]; simp [s₁, State.setArr]
        · exact absurd h' h

/-! ### The program -/

/-- The solver arenas, arrays 50 to 62. -/
def solverArrays : List ℕ := solverFields.map Field.array

theorem solverArrays_ge : ∀ a ∈ solverArrays, 50 ≤ a := by decide

theorem mem_solverArrays : ∀ a : ℕ, 50 ≤ a → a ≤ 62 → a ∈ solverArrays := by
  have h : ∀ i < 13, 50 + i ∈ solverArrays := by decide
  intro a h1 h2
  have := h (a - 50) (by omega)
  rwa [show 50 + (a - 50) = a by omega] at this

theorem solverFields_capacity (N M : ℕ) : ∀ f ∈ solverFields, f.capacity N M ≤ N + M + 1 := by
  intro f hf
  simp only [solverFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Field.capacity] <;> omega

/-- Clear the arenas and set the allocators and the flag. -/
def initProg : Cmd :=
  .seq (zeroProg solverArrays)
  (.seq (.assign 53 (.const 1))
  (.seq (.assign 54 (.const 1))
  (.seq (.assign 55 (.const 1))
  (.seq (.assign 35 (.const 1))
    (.assign 52 (.const 0))))))

/-- The solver of Part I, Section 6. -/
def solveProg : Cmd := .seq initProg vertexLoopProg

theorem restPot_eq (search : Search) (outgoing : Array (List ℕ)) (k : ℕ) :
    restPot search outgoing k =
      200 * (search.postorder.drop k).length + 500 * restEdges search outgoing k := by
  unfold restPot restEdges
  induction search.postorder.drop k with
  | nil => simp
  | cons u l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- The solver phase of the planarity test runs in linear time on the Word
RAM and computes `solve`. -/
theorem solveRamClaim_proved : PlanarityRamSolveClaim := by
  refine ⟨solveProg, 1000, 4, ?_⟩
  intro N M w search s hw hsearch hbound hnodup hpo hout harena
  have hin : SolveInput N M w search s := ⟨hw, hsearch, hbound, hout⟩
  -- Clear the arenas.
  obtain ⟨s₁, t₁, hx₁, ht₁, hregs₁, hkeep₁, hzero₁⟩ := zeroProg_spec (w := w) (L := N + M + 1)
    solverArrays s (fun a ha => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
      rw [harena f hf]
      exact solverFields_capacity N M f hf) (by omega)
  have hlenA : solverArrays.length = 13 := rfl
  let s₂ := ((((s₁.setReg 53 1).setReg 54 1).setReg 55 1).setReg 35 1).setReg 52 0
  have hx₂ : Exec w initProg s s₂ (t₁ + (2 + (2 + (2 + (2 + 2))))) :=
    Exec.seq hx₁ (Exec.seq (exec_setc (by omega)) (Exec.seq (exec_setc (by omega))
      (Exec.seq (exec_setc (by omega)) (Exec.seq (exec_setc (by omega)) (exec_setc (by omega))))))
  have harr₂ : s₂.arrs = s₁.arrs := rfl
  have hreg₂ : ∀ r : ℕ, r ≠ 35 → r ≠ 52 → r ≠ 53 → r ≠ 54 → r ≠ 55 → s₂.regs r = s.regs r := by
    intro r h1 h2 h3 h4 h5
    simp [s₂, h1, h2, h3, h4, h5, hregs₁]
  have hres₂ : s₂.arrs Field.result.array = List.replicate N 0 := by
    rw [harr₂, hzero₁ _ (by decide), harena Field.result (by simp [solverFields])]
    rfl
  -- The state before the vertex loop.
  have hc₂ : Common N M s s₂ := by
    refine ⟨fun a ha => ?_, fun r hr => hreg₂ r (by omega) (by omega) (by omega) (by omega)
      (by omega), ?_, ?_⟩
    · rw [harr₂, hkeep₁ a fun h => by have := solverArrays_ge a h; omega]
    · intro a h1 h2 x hx
      rw [harr₂, hzero₁ a (mem_solverArrays a h1 h2)] at hx
      rw [List.eq_of_mem_replicate hx]
      omega
    · intro f hf
      rw [harr₂, hzero₁ _ (List.mem_map_of_mem hf), List.length_replicate]
      exact harena f hf
  obtain ⟨hosz, htot, -⟩ := bucketOrder_facts N search.edges
  have hpoN : search.postorder.length ≤ N := hsearch.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hE := hin.edges_le
  have hrest : restEdges search (bucketOrder N search.edges) 0 ≤ M := by
    have := sum_le_arraySum List.length (bucketOrder N search.edges) search.postorder hnodup
      (fun v hv => by rw [hosz]; exact hpo v hv)
    simp only [restEdges, List.drop_zero]
    simp only [totalLength] at htot
    omega
  have hst : VertexState N M search s 0 (Array.replicate N none) s₂ := by
    refine ⟨hc₂, by simp [s₂], by simp [s₂], by omega, by simp, ?_, by simp [s₂], by simp [s₂],
      by simp [s₂], by simp [s₂]; omega, by simp [s₂]; omega, by simp [s₂]; omega⟩
    refine ⟨fun _ => 0, ⟨fun _ => [], fun _ => [], ?_, ?_, ?_⟩, rfl, rfl, ?_⟩
    · intro v hv
      have : slotOf N (Array.replicate N none) none none v = none := by
        unfold slotOf
        by_cases h : v < N
        · simp [h]
        · simp [h]
      rw [this]
      exact ⟨rfl, rfl, rfl⟩
    · intro v hv
      exact ⟨by simp, by simp, by simp [s₂]⟩
    · intro u hu v hv huv
      simp
    · intro v hv
      rw [hres₂]
      simp [hv]
  -- The vertex loop.
  obtain ⟨s', t, hx, hc', h35, ht⟩ := vertexLoop_spec hin hpo hst
  have hpot := restPot_eq search (bucketOrder N search.edges) 0
  simp only [List.drop_zero] at hpot
  refine ⟨s', _, Exec.seq hx₂ hx, ?_, fun r hr => hc'.2.1 r (Or.inl (Nat.lt_trans hr (by decide))),
    fun a ha => hc'.1 a (Nat.lt_trans ha (by decide)), h35⟩
  rw [hlenA] at ht₁
  omega

end GraphMinor.Compute.PlanarityRam
