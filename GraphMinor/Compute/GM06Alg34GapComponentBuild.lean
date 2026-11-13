module

public import GraphMinor.Compute.GM06Alg34ComponentMask
public import GraphMinor.Compute.GM06Alg34GapPayloadInput
public import GraphMinor.Compute.GM06Alg34GapComponentData
public import GraphMinor.Compute.GM06Alg34GapDiscLayout
import Mathlib.Tactic.Ring

/-!
# Materializing an augmented component branch

Search from the supplied component root, copy its marks into the
retained vertex mask, and run the complete augmented input builder.
Both arrays become the exact component input for VI (3.3)(iv).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Install the component selected in register 114 in both input arrays. -/
def gm06GapComponentBuildProg : Cmd :=
  .seq (.assign 187 (.reg 114)) (.seq gm06VertexBfsProg
    (.seq gm06ComponentMaskProg gm06GapPayloadBuildProg))

private theorem update_budget (n : ℕ) :
    2 + (26 * (n * n) + 23 * n + 26) + (16 * n + 9) +
      1200 * (n + 2) ^ 3 ≤ 1300 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The component update installs both exact finite induced payloads in
cubic time, reading only supplied arrays, computed CSR, and the selected label. -/
theorem gm06GapComponentBuildProg_exec (x : GM06DrawingData) (L : List (Fin x.n))
    (R : List (Fin x.regions.length)) (a : Fin x.n)
    (hL : x.cuffs = [L]) (hRlen : R.length = L.length)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hgap : s.arrs 47 = R.map Fin.val)
    (hselected : s.regs 114 = a.val) (hsize : s.regs 4 = x.n)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) :
    ∃ s' t, Exec (wordSize c x.size) gm06GapComponentBuildProg s s' t ∧
      t ≤ 1300 * (x.size + 2) ^ 3 ∧ s'.arrs 0 = (x.componentData a).words ∧
      s'.arrs 47 = (x.gapRegionsAfterDeletion (x.componentVertices a) L R).map Fin.val ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hsizew : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsizew
  have hw : 1 < 2 ^ wordSize c x.size := by
    have h := x.five_le_words_length
    have hh := x.words_length_le_size
    omega
  have hsquare := (Nat.mul_le_mul (x.counts_le_size.1.trans (by omega))
    (x.counts_le_size.1.trans (by omega))).trans_lt (sq_lt_two_pow_wordSize (n := x.size) hc2)
  let s₁ := s.setReg 187 a.val
  have hex₁ : Exec (wordSize c x.size) (.assign 187 (.reg 114)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hselected, a.isLt.trans hn])
  obtain ⟨s₂, t₂, hex₂, ht₂, hmarks₂, ha₂, hg₂⟩ :=
    gm06VertexBfsProg_exec x a hw hn hsquare (s := s₁)
      (by simpa [s₁] using hsize) (by simp [s₁]) hlists hlen
  obtain ⟨s₃, t₃, hex₃, ht₃, hmask₃, ha₃, _⟩ :=
    gm06ComponentMaskProg_exec x a hw hn hmarks₂
      ((hg₂ 4 (by decide)).trans hsize)
  have hgap₃ : s₃.arrs 47 = R.map Fin.val :=
    (ha₃ 47 (by decide)).trans ((ha₂ 47 (by decide) (by decide)).trans hgap)
  obtain ⟨s₄, t₄, hex₄, ht₄, hnewInput, hnewGap, harr₄⟩ :=
    gm06GapPayloadBuildProg_exec_list x (x.componentVertices a) L R hL hRlen hc
      ((ha₃ 0 (by decide)).trans ((ha₂ 0 (by decide) (by decide)).trans hinput)) hmask₃ hgap₃
  have hnsize := x.counts_le_size.1
  have hsq := Nat.mul_le_mul hnsize hnsize
  refine ⟨s₄, 2 + (t₂ + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, hnewInput, hnewGap, ?_⟩
  · exact (show 2 + (t₂ + (t₃ + t₄)) ≤
      2 + (26 * (x.size * x.size) + 23 * x.size + 26) + (16 * x.size + 9) +
        1200 * (x.size + 2) ^ 3 by omega).trans (update_budget x.size)
  · intro A hA
    exact (harr₄ A hA).trans ((ha₃ A (by omega)).trans (ha₂ A (by omega) (by omega)))

/-- Component materialization installs the exact augmented finite input
from its two internal arrays for every matching single-cuff layout. -/
theorem gm06GapComponentBuildProg_exec_input (X : GM06GapInput) (a : Fin X.drawing.n)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = X.drawing.words)
    (hgap : s.arrs 47 = X.discGapWords) (hselected : s.regs 114 = a.val)
    (hsize : s.regs 4 = X.drawing.n)
    (hlists : IsAdjList X.drawing.vertexGraph 30 31 32 (adjListOf X.drawing.vertexGraph) s)
    (hlen : (s.arrs 32).length = X.drawing.n * X.drawing.n) :
    ∃ s' t, Exec (wordSize c X.drawing.size) gm06GapComponentBuildProg s s' t ∧
      t ≤ 1300 * (X.drawing.size + 2) ^ 3 ∧
      s'.arrs 0 = (X.componentGapData a).drawing.words ∧
      s'.arrs 47 = (X.componentGapData a).discGapWords ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  obtain ⟨L, R, hL, hR, hRlen⟩ := hshape
  obtain ⟨s', t, he, ht, hbase, hnewgap, harr⟩ :=
    gm06GapComponentBuildProg_exec X.drawing L R a hL hRlen hc hinput
      (hgap.trans (X.discGapWords_singleton R hR)) hselected hsize hlists hlen
  exact ⟨s', t, he, ht, hbase,
    hnewgap.trans (X.inducedGapInput_discGapWords
      (X.drawing.componentVertices a) L R hL hR).symm, harr⟩

end GraphMinor.Compute
