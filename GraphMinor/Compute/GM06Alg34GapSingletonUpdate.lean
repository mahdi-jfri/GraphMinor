module

public import GraphMinor.Compute.GM06Alg34GapPayloadInput
public import GraphMinor.Compute.GM06Alg34MaskInit
public import GraphMinor.Compute.GM06Alg34SingletonData
public import GraphMinor.Compute.GM06Alg34GapDiscLayout
import Mathlib.Tactic.Ring

/-!
# Singleton deletion with exact gap incidence on the RAM

Read the vertex count, initialize the retained mask, and delete the
selected singleton vertex. The augmented payload builder then replaces
both the drawing input and its gap region list. This is the numeric
update used by the repeated singleton phase of VI (3.4).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Delete selected vertex 114 and install the drawing and gap payloads. -/
def gm06GapSingletonUpdateProg : Cmd :=
  .seq (.assign 100 (.read 0 (.const 0))) (.seq gm06InitVertexMaskProg
    (.seq gm06DeleteVertexProg gm06GapPayloadBuildProg))

private theorem update_budget (n : ℕ) :
    3 + (13 * n + 6) + (3 + 1200 * (n + 2) ^ 3) ≤ 1300 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The augmented singleton update computes exactly both finite
payloads of VI (3.3)(i) with a cubic time bound and logarithmic words. -/
theorem gm06GapSingletonUpdateProg_exec (x : GM06DrawingData)
    (L : List (Fin x.n)) (R : List (Fin x.regions.length)) (v : Fin x.n)
    (hL : x.cuffs = [L]) (hlen : R.length = L.length)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hgap : s.arrs 47 = R.map Fin.val) (hselected : s.regs 114 = v.val) :
    ∃ s' t, Exec (wordSize c x.size) gm06GapSingletonUpdateProg s s' t ∧
      t ≤ 1300 * (x.size + 2) ^ 3 ∧ s'.arrs 0 = (x.singletonData v).words ∧
      s'.arrs 47 = (x.gapRegionsAfterDeletion (x.singletonSurvivors v) L R).map Fin.val ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  have hsize : x.size < 2 ^ wordSize c x.size :=
    lt_two_pow_wordSize_of_le (by omega) (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by
    have h := x.five_le_words_length
    have hh := x.words_length_le_size
    omega
  let s₁ := s.setReg 100 x.n
  have hex₁ : Exec (wordSize c x.size) (.assign 100 (.read 0 (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hinput, x.words_layout,
      Nat.zero_lt_of_lt hw, hn])
  obtain ⟨s₂, t₂, hex₂, ht₂, hmask₂, ha₂, hg₂⟩ :=
    gm06InitVertexMaskProg_exec hw hn (s := s₁) (by simp [s₁])
  obtain ⟨s₃, hex₃, hmask₃, ha₃, _⟩ :=
    gm06DeleteVertexProg_exec (List.finRange x.n) v hn hmask₂
      (by rw [hg₂ 114 (by decide)]; simpa [s₁, State.setReg] using hselected)
  have hin₃ : s₃.arrs 0 = x.words :=
    (ha₃ 0 (by decide)).trans ((ha₂ 0 (by decide)).trans hinput)
  have hgap₃ : s₃.arrs 47 = R.map Fin.val :=
    (ha₃ 47 (by decide)).trans ((ha₂ 47 (by decide)).trans hgap)
  obtain ⟨s₄, t₄, hex₄, ht₄, hinput₄, hgap₄, harr₄⟩ :=
    gm06GapPayloadBuildProg_exec_list x (x.singletonSurvivors v) L R hL hlen hc hin₃ hmask₃ hgap₃
  refine ⟨s₄, 3 + (t₂ + (3 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_,
    hinput₄, hgap₄, ?_⟩
  · exact (show 3 + (t₂ + (3 + t₄)) ≤
      3 + (13 * x.size + 6) + (3 + 1200 * (x.size + 2) ^ 3) by
      have hh := x.counts_le_size.1
      omega).trans (update_budget x.size)
  · intro A hA
    exact (harr₄ A hA).trans ((ha₃ A (by omega)).trans (ha₂ A (by omega)))

/-- The singleton update installs the exact augmented finite input from
its two internal arrays, for every matching single-cuff layout. -/
theorem gm06GapSingletonUpdateProg_exec_input (X : GM06GapInput) (v : Fin X.drawing.n)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = X.drawing.words)
    (hgap : s.arrs 47 = X.discGapWords) (hselected : s.regs 114 = v.val) :
    ∃ s' t, Exec (wordSize c X.drawing.size) gm06GapSingletonUpdateProg s s' t ∧
      t ≤ 1300 * (X.drawing.size + 2) ^ 3 ∧
      s'.arrs 0 = (X.singletonGapData v).drawing.words ∧
      s'.arrs 47 = (X.singletonGapData v).discGapWords ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  obtain ⟨L, R, hL, hR, hlen⟩ := hshape
  obtain ⟨s', t, he, ht, hbase, hnewgap, harr⟩ :=
    gm06GapSingletonUpdateProg_exec X.drawing L R v hL hlen hc hinput
      (hgap.trans (X.discGapWords_singleton R hR)) hselected
  exact ⟨s', t, he, ht, hbase,
    hnewgap.trans (X.inducedGapInput_discGapWords (X.drawing.singletonSurvivors v) L R hL hR).symm,
    harr⟩

end GraphMinor.Compute
