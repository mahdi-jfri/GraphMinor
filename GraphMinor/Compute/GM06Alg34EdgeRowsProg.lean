module

public import GraphMinor.Compute.GM06Alg34EdgeRowsLoop

/-!
# Building the supplied edge closure rows from the input header

Start the packed edge labels immediately after the vertices and reset
the endpoint cursor to the supplied endpoint section. The header's edge
count controls the verified scan, whose output is the exact sequence
of closure-row updates for the old edges.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Initialize the edge closure scan from the supplied vertex/edge counts. -/
def gm06EdgeRowsProg : Cmd :=
  .seq (.assign 171 (.reg 100)) (.seq (.assign 175 (.reg 101))
    (.seq (.assign 103 (.const 3)) gm06EdgeRowsLoopProg))

/-- Supplied endpoint labels satisfy the packed cell-column bounds. -/
theorem GM06DrawingData.raw_ends_valid (x : GM06DrawingData) :
    ∀ p ∈ x.raw.ends, p.1 < x.cellCount ∧ p.2 < x.cellCount := by
  intro p hp
  change p ∈ x.ends.map (fun e => (e.1.val, e.2.val)) at hp
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hp
  have h₁ := e.1.isLt
  have h₂ := e.2.isLt
  unfold GM06DrawingData.cellCount
  constructor <;> omega

/-- The actual endpoint section produces exactly the supplied old-edge
closure rows, with linear RAM work and preserved drawing/header arrays. -/
theorem gm06EdgeRowsProg_exec {w : ℕ} (x : GM06DrawingData) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hoff : 3 + 2 * x.ends.length < 2 ^ w) {s : State}
    (hs : AtStream 0 3 (x.endpointWords ++ tail) s)
    (hvertex : s.regs 100 = x.n) (hedge : s.regs 101 = x.ends.length)
    (hNr : s.regs 170 = x.cellCount) (hcap : (s.arrs 12).length = x.cellCount * x.cellCount) :
    ∃ s' t, Exec w gm06EdgeRowsProg s s' t ∧ t ≤ 58 * x.ends.length + 7 ∧
      s'.arrs 12 = gm06EdgeRows x.cellCount x.n x.raw.ends (s.arrs 12) ∧
      s'.regs 103 = 3 + 2 * x.ends.length ∧ s'.regs 171 = x.n + x.ends.length ∧
      AtStream 0 (3 + 2 * x.ends.length) tail s' ∧
      (∀ A : ℕ, A ≠ 12 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 132 → q ≠ 133 → q ≠ 171 →
        q ≠ 173 → q ≠ 174 → q ≠ 175 → s'.regs q = s.regs q) := by
  have hn : x.n < 2 ^ w := by unfold GM06DrawingData.cellCount at hN; omega
  have hm : x.ends.length < 2 ^ w := by unfold GM06DrawingData.cellCount at hN; omega
  have hfit : x.n + x.raw.ends.length ≤ x.cellCount := by
    simp only [GM06DrawingData.raw, List.length_map, GM06DrawingData.cellCount]
    omega
  let s₁ := s.setReg 171 x.n
  have he₁ : Exec w (.assign 171 (.reg 100)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hvertex, hn])
  let s₂ := s₁.setReg 175 x.ends.length
  have he₂ : Exec w (.assign 175 (.reg 101)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hedge, hm])
  let s₃ := s₂.setReg 103 3
  have he₃ : Exec w (.assign 103 (.const 3)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 3 < 2 ^ w by omega])
  have hs₃ : AtStream 0 3 (gm06EdgeWords x.raw.ends ++ tail) s₃ := by
    rw [gm06EdgeWords_raw]
    exact hs.of_arr_eq rfl
  obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hp₄, hi₄, _, hs₄, ha₄, hr₄⟩ :=
    gm06EdgeRowsLoopProg_exec (s := s₃) x.raw.ends tail hw hN hsquare hfit
      (by simpa only [GM06DrawingData.raw, List.length_map] using hoff) x.raw_ends_valid
      hs₃ (by simp [s₃]) (by simp [s₃, s₂, GM06DrawingData.raw])
      (by simp [s₃, s₂, s₁, hNr]) (by simp [s₃, s₂, s₁]) hcap
  have hex : Exec w gm06EdgeRowsProg s s₄ (2 + (2 + (2 + t₄))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  simp only [GM06DrawingData.raw, List.length_map] at ht₄ hp₄ hi₄ hs₄
  refine ⟨s₄, _, hex, by omega, hbuf₄, hp₄, hi₄, hs₄, ha₄, ?_⟩
  intro q hqp hqv hqA hqB hqi hqr hqs hqn
  rw [hr₄ q hqp hqv hqA hqB hqi hqr hqs hqn]
  change (s₂.setReg 103 3).regs q = _
  rw [State.setReg_regs_ne _ _ hqp, State.setReg_regs_ne _ _ hqn,
    State.setReg_regs_ne _ _ hqi]

end GraphMinor.Compute
