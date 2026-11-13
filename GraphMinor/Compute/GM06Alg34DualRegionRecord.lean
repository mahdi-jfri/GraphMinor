module

public import GraphMinor.Compute.GM06Alg34DualRegionVerticesProg
public import GraphMinor.Compute.GM06Alg34DualRegionEdgesProg
public import GraphMinor.Compute.GM06Alg34DualSelectedField

/-!
# Writing a complete dual region boundary record

For the selected old vertex, emit the old region labels meeting it,
then the old edge labels having it as an end. These are exactly the
two transposed boundary lists of its dual region. Each selected list
is written with its length, preserving the previous output prefix.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The two length-prefixed boundary lists of a dual region. -/
def gm06DualRegionRecordWords (x : GM06DrawingData) (v : Fin x.n) : List ℕ :=
  GM06DrawingData.listWords ((x.dualRegionVertices v).map Fin.val) ++
    GM06DrawingData.listWords ((x.dualRegionEdges v).map Fin.val)

/-- Emit both dual boundary lists indexed by old vertex register 7600. -/
def gm06DualRegionRecordProg : Cmd :=
  .seq gm06DualRegionVerticesProg (.seq gm06DualSelectedFieldProg
    (.seq gm06DualRegionEdgesProg gm06DualSelectedFieldProg))

/-- One transposed dual region record is written exactly, with linear
work in the supplied edge and region counts. -/
theorem gm06DualRegionRecordProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (v : Fin x.n) {pre : List ℕ} {s : State}
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hRspan : x.regions.length + 2 < 2 ^ w) (hEspan : x.ends.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hvertex : s.regs 7600 = v.val)
    (hregions : s.arrs 52 = List.range x.regions.length) (hedges : s.arrs 51 = List.range x.ends.length)
    (hbuf : IsPrefixBuffer 55 pre ((gm06DualRegionRecordWords x v).length + cap) s)
    (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + (gm06DualRegionRecordWords x v).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualRegionRecordProg s s' t ∧
      t ≤ 200 * (x.regions.length + x.ends.length + 2) ∧
      IsPrefixBuffer 55 (pre ++ gm06DualRegionRecordWords x v) cap s' ∧
      s'.regs 7804 = (pre ++ gm06DualRegionRecordWords x v).length ∧
      (∀ A : ℕ, A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7820 → r < 7601 ∨ 7605 < r → r ≠ 7804 → s'.regs r = s.regs r) := by
  let V := (x.dualRegionVertices v).map Fin.val
  let E := (x.dualRegionEdges v).map Fin.val
  have hV : V.length ≤ x.regions.length := by
    simpa only [V, GM06DrawingData.dualRegionVertices, List.length_map, List.length_finRange] using
      List.length_filter_le (fun r => decide (v ∈ x.regions[r].vertices)) (List.finRange x.regions.length)
  have hE : E.length ≤ x.ends.length := by
    simpa only [E, GM06DrawingData.dualRegionEdges, List.length_map, List.length_finRange] using
      List.length_filter_le (fun e => decide (x.ends[e].1 = v ∨ x.ends[e].2 = v)) (List.finRange x.ends.length)
  have hVw : ∀ y ∈ V, y < 2 ^ w := by
    intro y hy
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hy
    exact r.isLt.trans (by omega)
  have hEw : ∀ y ∈ E, y < 2 ^ w := by
    intro y hy
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hy
    exact e.isLt.trans (by omega)
  have hlen : (gm06DualRegionRecordWords x v).length = 2 + V.length + E.length := by
    simp only [gm06DualRegionRecordWords, GM06DrawingData.listWords, List.length_append,
      List.length_cons, V, E]; omega
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hc₁, ha₁, hg₁⟩ :=
    gm06DualRegionVerticesProg_exec x v hw hN hsquare hRspan hmat hstride hn hm hvertex hregions
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, _, ha₂, hg₂⟩ :=
    gm06DualSelectedFieldProg_exec V hw hVw (by omega)
      (by simpa only [IsPrefixBuffer, List.length_map] using hb₁)
      (by simpa only [V, List.length_map] using hc₁)
      (by have hb := hbuf.of_arr_eq (ha₁ 55 (by decide));
          have heq : (gm06DualRegionRecordWords x v).length + cap =
            1 + V.length + (1 + E.length + cap) := by omega
          exact heq ▸ hb)
      ((hg₁ 7804 (Or.inr (by decide))).trans hpos)
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hc₃, ha₃, hg₃⟩ :=
    gm06DualRegionEdgesProg_exec x v hw hN hsquare hEspan
      ((ha₂ 12 (by decide) (by decide)).trans ((ha₁ 12 (by decide)).trans hmat))
      ((hg₂ 170 (by decide) (by decide)).trans ((hg₁ 170 (Or.inl (by decide))).trans hstride))
      ((hg₂ 100 (by decide) (by decide)).trans ((hg₁ 100 (Or.inl (by decide))).trans hn))
      ((hg₂ 7600 (by decide) (by decide)).trans ((hg₁ 7600 (Or.inl (by decide))).trans hvertex))
      ((ha₂ 51 (by decide) (by decide)).trans ((ha₁ 51 (by decide)).trans hedges))
  obtain ⟨s₄, t₄, he₄, ht₄, hb₄, hp₄, _, ha₄, hg₄⟩ :=
    gm06DualSelectedFieldProg_exec E hw hEw
      (by simp only [List.length_append, GM06DrawingData.listWords, List.length_cons]; omega)
      (by simpa only [IsPrefixBuffer, List.length_map] using hb₃)
      (by simpa only [E, List.length_map] using hc₃)
      (hb₂.of_arr_eq (ha₃ 55 (by decide))) ((hg₃ 7804 (Or.inr (by decide))).trans hp₂)
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    by omega, ?_, ?_, ?_, ?_⟩
  · simpa only [gm06DualRegionRecordWords, List.append_assoc] using hb₄
  · simpa only [gm06DualRegionRecordWords, List.append_assoc] using hp₄
  · intro A h54 h55 h56
    exact (ha₄ A h55 h56).trans ((ha₃ A h54).trans ((ha₂ A h55 h56).trans (ha₁ A h54)))
  · intro r hr hrange h7804
    exact (hg₄ r hr h7804).trans ((hg₃ r hrange).trans
      ((hg₂ r hr h7804).trans (hg₁ r hrange)))

end GraphMinor.Compute
