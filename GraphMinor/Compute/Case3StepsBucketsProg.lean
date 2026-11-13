module

public import GraphMinor.Compute.Case3StepsBucketsLoopProg
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Computing ordered buckets for all positive multigraph pairs

The pair count is read from the compact multigraph encoding. Empty bucket
heads hold this count as their sentinel, while counts and next pointers start
at zero. Reverse insertion then computes every ordered owner bucket with
linear work in the number of stored pairs and candidate labels.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Initialize bucket storage and insert all positive pairs in reverse order. -/
def case3BucketsProg : Cmd :=
  .seq (.assign 64 (.read 3 (.const 1)))
    (.seq (fillArrProg 35 52 64 65)
      (.seq (.alloc 36 (.reg 64))
        (.seq (.alloc 37 (.reg 52))
          (.seq (.assign 65 (.reg 64)) case3BucketsLoopProg))))

/-- The ordered pair buckets are computed in linear pair and candidate count.
Each record still refers to its full multiplicity word in the input encoding. -/
theorem case3BucketsProg_exec {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w)
    (hL : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hD : s.arrs 3 = D.enc) (hloop : s.arrs 33 = List.ofFn (case3OrderedLoopLabel x Z))
    (hmat : s.arrs 34 = case3EdgeMatrixPrefix x Z (case3InputEdges x).length)
    (hrn : s.regs 14 = x.n) (hrL : s.regs 52 = x.n + (case3InputEdges x).length) :
    ∃ s' t, Exec w case3BucketsProg s s' t ∧
      t ≤ 12 * (x.n + (case3InputEdges x).length) + 43 * D.numActivePairs + 14 ∧
      s'.arrs 35 = case3BucketHeads (case3ActivePairOwner x D Z)
        (x.n + (case3InputEdges x).length) 0 ∧
      s'.arrs 36 = case3BucketNext (case3ActivePairOwner x D Z) 0 ∧
      s'.arrs 37 = case3BucketCounts (case3ActivePairOwner x D Z)
        (x.n + (case3InputEdges x).length) 0 ∧ s'.regs 64 = D.numActivePairs ∧
      (∀ a, a ≠ 35 → a ≠ 36 → a ≠ 37 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 64 → r ≠ 65 → r ≠ 66 → r ≠ 67 → r ≠ 68 → r ≠ 69 →
        s'.regs r = s.regs r) := by
  let L := x.n + (case3InputEdges x).length
  let A := D.numActivePairs
  have hLw : L < 2 ^ w := hL
  have hAw : A < 2 ^ w := by dsimp only [A]; omega
  have h1 : 1 < 2 ^ w := by omega
  obtain ⟨hi, hg⟩ := enc_getElem_one D [] (by simpa only [List.append_nil] using hD)
  let s₀ := s.setReg 64 A
  have hex₀ : Exec w (.assign 64 (.read 3 (.const 1))) s s₀ 3 :=
    .assign (by simp [Expr.eval, checkWord, h1, hi, hg, hAw, A])
  obtain ⟨s₁, t₁, hex₁, ht₁, hfill₁, harr₁, hreg₁⟩ :=
    fillArrProg_exec 35 52 64 65 (by decide) (by decide) h1 hL hAw (s := s₀)
      (by rw [State.setReg_regs_ne _ _ (by decide)]; exact hrL) (State.setReg_regs_self ..)
  let s₂ := s₁.setArr 36 (List.replicate A 0)
  let s₃ := s₂.setArr 37 (List.replicate L 0)
  let s₄ := s₃.setReg 65 A
  have hrA₁ : s₁.regs 64 = A := by rw [hreg₁ 64 (by decide)]; exact State.setReg_regs_self ..
  have hrL₁ : s₁.regs 52 = L := by
    rw [hreg₁ 52 (by decide), State.setReg_regs_ne _ _ (by decide)]
    exact hrL
  have hex₂ : Exec w (.alloc 36 (.reg 64)) s₁ s₂ (1 + A) :=
    .alloc (by simp only [Expr.eval, checkWord, hrA₁, hAw, ↓reduceIte])
  have hex₃ : Exec w (.alloc 37 (.reg 52)) s₂ s₃ (1 + L) :=
    .alloc (by simp only [Expr.eval, checkWord, s₂, State.setArr_regs, hrL₁, hLw, ↓reduceIte])
  have hex₄ : Exec w (.assign 65 (.reg 64)) s₃ s₄ 2 :=
    .assign (by simp only [Expr.eval, checkWord, s₃, s₂, State.setArr_regs, hrA₁, hAw, ↓reduceIte])
  have harr₄ (a : ℕ) (h35 : a ≠ 35) (h36 : a ≠ 36) (h37 : a ≠ 37) :
      s₄.arrs a = s.arrs a := by
    simp only [s₄, s₃, s₂, State.setReg_arrs, State.setArr_arrs_ne _ _ h37,
      State.setArr_arrs_ne _ _ h36, harr₁ a h35, s₀]
  have hheads₄ : s₄.arrs 35 = case3BucketHeads (case3ActivePairOwner x D Z) L A := by
    simp only [s₄, s₃, s₂, State.setReg_arrs,
      State.setArr_arrs_ne _ _ (show (35 : ℕ) ≠ 37 by decide),
      State.setArr_arrs_ne _ _ (show (35 : ℕ) ≠ 36 by decide), hfill₁,
      A, L, case3BucketHeads_done]
  have hnext₄ : s₄.arrs 36 = case3BucketNext (case3ActivePairOwner x D Z) A := by
    simp only [s₄, s₃, s₂, State.setReg_arrs,
      State.setArr_arrs_ne _ _ (show (36 : ℕ) ≠ 37 by decide), State.setArr_arrs_self,
      A, case3BucketNext_done]
  have hcounts₄ : s₄.arrs 37 = case3BucketCounts (case3ActivePairOwner x D Z) L A := by
    simp only [s₄, s₃, State.setReg_arrs, State.setArr_arrs_self, A, case3BucketCounts_done]
  have hrn₄ : s₄.regs 14 = x.n := by
    simp only [s₄, s₃, s₂, State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 65 by decide),
      State.setArr_regs, hreg₁ 14 (by decide), s₀,
      State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 64 by decide), hrn]
  obtain ⟨s₅, t₅, hex₅, ht₅, hheads₅, hnext₅, hcounts₅, harr₅, hreg₅⟩ :=
    case3BucketsLoopProg_exec x D hG Z hdiv hw hn hsquare hA hL A le_rfl
      (s := s₄) ((harr₄ 3 (by decide) (by decide) (by decide)).trans hD)
      ((harr₄ 33 (by decide) (by decide) (by decide)).trans hloop)
      ((harr₄ 34 (by decide) (by decide) (by decide)).trans hmat)
      hheads₄ hnext₄ hcounts₄ hrn₄ (State.setReg_regs_self ..)
  refine ⟨s₅, 3 + (t₁ + ((1 + A) + ((1 + L) + (2 + t₅)))),
    .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))),
    by dsimp only [L, A] at *; omega, hheads₅, hnext₅, hcounts₅, ?_, ?_, ?_⟩
  · rw [hreg₅ 64 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s₄, s₃, s₂, State.setReg_regs_ne _ _ (show (64 : ℕ) ≠ 65 by decide),
      State.setArr_regs, hrA₁, A]
  · intro a h35 h36 h37
    exact (harr₅ a h35 h36 h37).trans (harr₄ a h35 h36 h37)
  · intro r h64 h65 h66 h67 h68 h69
    rw [hreg₅ r h65 h66 h67 h68 h69]
    simp only [s₄, s₃, s₂, State.setReg_regs_ne _ _ h65, State.setArr_regs,
      hreg₁ r h65, s₀, State.setReg_regs_ne _ _ h64]

end GraphMinor.Compute
