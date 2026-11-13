module

public import GraphMinor.Compute.GM06Alg34RegionRowsLoop
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# Building the supplied region closure rows from the drawing header

The parsed header supplies the vertex, edge, and region counts. Start
the packed region labels after the vertices and edges and run the
verified counted scan. The label bounds carried by the plain input
lists prove every boundary column fits in the cell matrix.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Initialize the packed region label and remaining count from the supplied header. -/
def gm06RegionRowsProg : Cmd :=
  .seq (.assign 171 (.op .add (.reg 100) (.reg 101)))
    (.seq (.assign 175 (.reg 102)) gm06RegionRowsLoopProg)

/-- The actual supplied region lists satisfy the packed column bounds. -/
theorem GM06DrawingData.raw_regions_valid (x : GM06DrawingData) :
    ∀ r ∈ x.raw.regions, (∀ v ∈ r.1, v < x.cellCount) ∧
      (∀ e ∈ r.2, x.n + e < x.cellCount) := by
  intro r hr
  change r ∈ x.regions.map (fun r => (r.vertices.map Fin.val, r.edges.map Fin.val)) at hr
  obtain ⟨R, _, rfl⟩ := List.mem_map.mp hr
  constructor
  · intro v hv
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
    have hh := v.isLt
    unfold GM06DrawingData.cellCount
    omega
  · intro e he
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp he
    have hh := e.isLt
    unfold GM06DrawingData.cellCount
    omega

/-- Reading the supplied region section marks exactly its consecutive
closure rows, with linear work and preserved drawing/header arrays. -/
theorem gm06RegionRowsProg_exec {w off : ℕ} (x : GM06DrawingData) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hoff : off + x.regionWords.length < 2 ^ w) {s : State}
    (hs : AtStream 0 off (x.regionWords ++ tail) s) (hp : s.regs 103 = off)
    (hvertex : s.regs 100 = x.n) (hedge : s.regs 101 = x.ends.length)
    (hregion : s.regs 102 = x.regions.length) (hNr : s.regs 170 = x.cellCount)
    (hcap : (s.arrs 12).length = x.cellCount * x.cellCount) :
    ∃ s' t, Exec w gm06RegionRowsProg s s' t ∧ t ≤ 25 * x.regionWords.length + 7 ∧
      s'.arrs 12 = gm06RegionRows x.cellCount x.n (x.n + x.ends.length) x.raw.regions (s.arrs 12) ∧
      s'.regs 103 = off + x.regionWords.length ∧ s'.regs 171 = x.cellCount ∧
      AtStream 0 (off + x.regionWords.length) tail s' ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 171 → q ≠ 172 → q ≠ 173 →
        q ≠ 174 → q ≠ 175 → s'.regs q = s.regs q) := by
  have hn : x.n < 2 ^ w := by unfold GM06DrawingData.cellCount at hN; omega
  have hm : x.ends.length < 2 ^ w := by unfold GM06DrawingData.cellCount at hN; omega
  have hr : x.regions.length < 2 ^ w := by unfold GM06DrawingData.cellCount at hN; omega
  have hstart : x.n + x.ends.length < 2 ^ w := by unfold GM06DrawingData.cellCount at hN; omega
  have hfit : (x.n + x.ends.length) + x.raw.regions.length = x.cellCount := by
    simp only [GM06DrawingData.raw, List.length_map, GM06DrawingData.cellCount]
    omega
  let s₁ := s.setReg 171 (x.n + x.ends.length)
  have he₁ : Exec w (.assign 171 (.op .add (.reg 100) (.reg 101))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvertex, hedge, hn, hm, hstart])
  let s₂ := s₁.setReg 175 x.regions.length
  have he₂ : Exec w (.assign 175 (.reg 102)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hregion, hr])
  obtain ⟨s₃, t₃, he₃, ht₃, hbuf₃, hp₃, hi₃, _, hs₃, ha₃, hr₃⟩ :=
    gm06RegionRowsLoopProg_exec (s := s₂) x.raw.regions tail hw hN hn hsquare hfit.le hoff
      x.raw_regions_valid (hs.of_arr_eq (s' := s₂) rfl) (by simp [s₂, s₁, hp])
      (by simp [s₂, GM06DrawingData.raw]) (by simp [s₂, s₁, hNr])
      (by simp [s₂, s₁]) (by simp [s₂, s₁, hvertex]) hcap
  have hex : Exec w gm06RegionRowsProg s s₃ (4 + (2 + t₃)) := .seq he₁ (.seq he₂ he₃)
  change t₃ ≤ 25 * x.regionWords.length + 1 at ht₃
  refine ⟨s₃, _, hex, by omega, hbuf₃, hp₃, hi₃.trans hfit, hs₃, ?_, ?_⟩
  · exact ha₃
  · intro q hqp hqv hqi hqc hqr hqs hqn
    rw [hr₃ q hqp hqv hqi hqc hqr hqs hqn]
    change (s₁.setReg 175 x.regions.length).regs q = _
    rw [State.setReg_regs_ne _ _ hqn, State.setReg_regs_ne _ _ hqi]

end GraphMinor.Compute
