module

public import GraphMinor.Compute.GM06Alg34InitCellMatrix
public import GraphMinor.Compute.GM06Alg34ClosureMatrixData
public import GraphMinor.Compute.GM06Alg34EdgeRowsProg
public import GraphMinor.Compute.GM06Alg34RegionRowsProg

/-!
# Constructing the complete supplied-cell closure matrix on the RAM

Allocate the square cell matrix and run the vertex, edge, and region
row passes in that order. The supplied header initializes each pass.
The endpoint and region streams are read from the original input, and
the cursor finishes at its cuff section. The exact finite matrix and
a quadratic allocation bound are proved together.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Allocate and fill every supplied vertex, edge, and region closure row. -/
def gm06ClosureRowsProg : Cmd :=
  .seq gm06InitCellMatrixProg (.seq gm06VertexRowsProg
    (.seq gm06EdgeRowsProg gm06RegionRowsProg))

/-- The three supplied row passes construct exactly the finite closure
matrix, preserving the original input and header counts. -/
theorem gm06ClosureRowsProg_exec {w : ℕ} (x : GM06DrawingData) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hoff : x.cuffOffset < 2 ^ w) {s : State}
    (hs : AtStream 0 3 (x.endpointWords ++ (x.regionWords ++ tail)) s)
    (hvertex : s.regs 100 = x.n) (hedge : s.regs 101 = x.ends.length)
    (hregion : s.regs 102 = x.regions.length) :
    ∃ s' t, Exec w gm06ClosureRowsProg s s' t ∧
      t ≤ x.cellCount * x.cellCount + 24 * x.n + 58 * x.ends.length + 25 * x.regionWords.length + 28 ∧
      s'.arrs 12 = gm06ClosureMatrixData x ∧ s'.regs 170 = x.cellCount ∧
      s'.regs 103 = x.cuffOffset ∧ AtStream 0 x.cuffOffset tail s' ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = x.regions.length ∧
      (∀ A : ℕ, A ≠ 12 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 100 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, he₁, hbuf₁, hN₁, ha₁, hr₁⟩ :=
    gm06InitCellMatrixProg_exec (n := x.n) (m := x.ends.length) (r := x.regions.length)
      hN hsquare hvertex hedge hregion
  have hn₁ : s₁.regs 100 = x.n := (hr₁ 100 (by decide)).trans hvertex
  have hm₁ : s₁.regs 101 = x.ends.length := (hr₁ 101 (by decide)).trans hedge
  have hrgn₁ : s₁.regs 102 = x.regions.length := (hr₁ 102 (by decide)).trans hregion
  have hcap₁ : (s₁.arrs 12).length = x.cellCount * x.cellCount := by
    rw [hbuf₁, List.length_replicate]
    rfl
  have hnN : x.n ≤ x.cellCount := by unfold GM06DrawingData.cellCount; omega
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, _, ha₂, hr₂⟩ :=
    gm06VertexRowsProg_exec hw hN hsquare hnN hN₁ hn₁ hcap₁
  have hkeep₂ : ∀ q : ℕ, q < 109 → s₂.regs q = s₁.regs q := by
    intro q hq
    exact hr₂ q (by omega) (by omega) (by omega) (by omega) (by omega)
  have hN₂ : s₂.regs 170 = x.cellCount :=
    (hr₂ 170 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN₁
  have hcap₂ : (s₂.arrs 12).length = x.cellCount * x.cellCount := by
    rw [hbuf₂, gm06OwnCellRows_length, hcap₁]
  have hs₂ : AtStream 0 3 (x.endpointWords ++ (x.regionWords ++ tail)) s₂ :=
    hs.of_arr_eq ((ha₂ 0 (by decide)).trans (ha₁ 0 (by decide)))
  have hend : 3 + 2 * x.ends.length < 2 ^ w := by
    unfold GM06DrawingData.cuffOffset at hoff
    omega
  obtain ⟨s₃, t₃, he₃, ht₃, hbuf₃, hp₃, _, hs₃, ha₃, hr₃⟩ :=
    gm06EdgeRowsProg_exec x (x.regionWords ++ tail) hw hN hsquare hend hs₂
      ((hkeep₂ 100 (by decide)).trans hn₁) ((hkeep₂ 101 (by decide)).trans hm₁) hN₂ hcap₂
  have hkeep₃ : ∀ q : ℕ, q < 103 → s₃.regs q = s₂.regs q := by
    intro q hq
    exact hr₃ q (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  have hN₃ : s₃.regs 170 = x.cellCount :=
    (hr₃ 170 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hN₂
  have hcap₃ : (s₃.arrs 12).length = x.cellCount * x.cellCount := by
    rw [hbuf₃, gm06EdgeRows_length, hcap₂]
  obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hp₄, _, hs₄, ha₄, hr₄⟩ :=
    gm06RegionRowsProg_exec x tail hw hN hsquare hoff hs₃ hp₃
      ((hkeep₃ 100 (by decide)).trans ((hkeep₂ 100 (by decide)).trans hn₁))
      ((hkeep₃ 101 (by decide)).trans ((hkeep₂ 101 (by decide)).trans hm₁))
      ((hkeep₃ 102 (by decide)).trans ((hkeep₂ 102 (by decide)).trans hrgn₁)) hN₃ hcap₃
  have hkeep₄ : ∀ q : ℕ, q < 103 → s₄.regs q = s₃.regs q := by
    intro q hq
    exact hr₄ q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hN₄ : s₄.regs 170 = x.cellCount :=
    (hr₄ 170 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hN₃
  have hex : Exec w gm06ClosureRowsProg s s₄
      ((x.cellCount * x.cellCount + 9) + (t₂ + (t₃ + t₄))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  refine ⟨s₄, _, hex, by omega, ?_, hN₄, hp₄, hs₄, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbuf₄, hbuf₃, hbuf₂, hbuf₁]
    rfl
  · exact (hkeep₄ 100 (by decide)).trans ((hkeep₃ 100 (by decide)).trans
      ((hkeep₂ 100 (by decide)).trans hn₁))
  · exact (hkeep₄ 101 (by decide)).trans ((hkeep₃ 101 (by decide)).trans
      ((hkeep₂ 101 (by decide)).trans hm₁))
  · exact (hkeep₄ 102 (by decide)).trans ((hkeep₃ 102 (by decide)).trans
      ((hkeep₂ 102 (by decide)).trans hrgn₁))
  · intro A hA
    exact (ha₄ A hA).trans ((ha₃ A hA).trans ((ha₂ A hA).trans (ha₁ A hA)))
  · intro q hq
    exact (hkeep₄ q (by omega)).trans ((hkeep₃ q (by omega)).trans
      ((hkeep₂ q (by omega)).trans (hr₁ q (by omega))))

end GraphMinor.Compute
