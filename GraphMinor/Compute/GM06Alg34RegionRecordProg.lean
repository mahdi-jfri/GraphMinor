module

public import GraphMinor.Compute.GM06Alg34RegionRecordWords

/-!
# Writing a complete recomputed region record

Append the new vertex boundary field, then the new edge boundary field.
The first field's size bound leaves the required word and buffer space
for the second. The resulting stream record is exactly the induced
region boundary record associated with the source component.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append the vertex and edge boundary fields of one new region. -/
def gm06RegionRecordProg : Cmd :=
  .seq gm06AppendBoundaryVertexProg gm06AppendBoundaryEdgeProg

/-- One complete recomputed region record is written exactly within a
quadratic bound, preserving the source graph and component arrays. -/
theorem gm06RegionRecordProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (pfx : List ℕ) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false)
    (hout : pfx.length + 2 + x.n + x.ends.length < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hvertexMask : s.arrs 4 = gm06VertexMask vs) (hvertexRanks : s.arrs 5 = gm06VertexRanks vs)
    (hedgeMask : s.arrs 6 = gm06EdgeMask x vs) (hedgeRanks : s.arrs 7 = gm06EdgeRanks x vs)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hbuf : IsPrefixBuffer 10 pfx ((gm06RegionRecordWords x vs a).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06RegionRecordProg s s' t ∧
      t ≤ (18 * x.cellCount + 72) * (x.n + x.ends.length) + 62 ∧
      IsPrefixBuffer 10 (pfx ++ gm06RegionRecordWords x vs a) cap s' ∧
      s'.regs 143 = (pfx ++ gm06RegionRecordWords x vs a).length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 10 → j ≠ 11 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q < 210 → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 143 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        q ≠ 207 → q ≠ 208 → q ≠ 209 → s'.regs q = s.regs q) := by
  let V := GM06DrawingData.listWords (((x.inducedRegionBoundary vs a).vertices).map Fin.val)
  have hbufV : IsPrefixBuffer 10 pfx
      (1 + (x.inducedRegionBoundary vs a).vertices.length +
        (1 + (x.inducedRegionBoundary vs a).edges.length + cap)) s := by
    simpa only [gm06RegionRecordWords, List.length_append, GM06DrawingData.listWords,
      List.length_cons, List.length_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbuf
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hcursor₁, harr₁, hreg₁⟩ :=
    gm06AppendBoundaryVertexProg_exec x vs a pfx hw hN hsquare ha (by omega)
      hmarks hmat hc hvertexMask hvertexRanks hn hbufV hcursor
  have hreg : ∀ q : ℕ, q = 100 ∨ q = 101 ∨ q = 170 → s₁.regs q = s.regs q := by
    intro q hq
    apply hreg₁ q <;> rcases hq with rfl | rfl | rfl <;> decide
  have hboundV := gm06RegionBoundaryVertices_length_le x vs a
  have houtE : (pfx ++ V).length + 1 + x.ends.length < 2 ^ w := by
    simp only [V, List.length_append, GM06DrawingData.listWords, List.length_cons, List.length_map]
    omega
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hcursor₂, harr₂, hreg₂⟩ :=
    gm06AppendBoundaryEdgeProg_exec x vs a (pfx ++ V) hw hN hsquare ha houtE
      ((harr₁ _ (by decide) (by decide) (by decide)).trans hmarks)
      ((harr₁ _ (by decide) (by decide) (by decide)).trans hmat)
      ((hreg 170 (Or.inr (Or.inr rfl))).trans hc)
      ((harr₁ _ (by decide) (by decide) (by decide)).trans hedgeMask)
      ((harr₁ _ (by decide) (by decide) (by decide)).trans hedgeRanks)
      ((hreg 100 (Or.inl rfl)).trans hn) ((hreg 101 (Or.inr (Or.inl rfl))).trans hm)
      hbuf₁ hcursor₁
  refine ⟨s₂, t₁ + t₂, Exec.seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_add]
    omega
  · simpa only [gm06RegionRecordWords, V, List.append_assoc] using hbuf₂
  · simpa only [gm06RegionRecordWords, V, List.append_assoc] using hcursor₂
  · intro j hj₁ hj₂ hj₃; exact (harr₂ j hj₁ hj₂ hj₃).trans (harr₁ j hj₁ hj₂ hj₃)
  · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₉ hq₁₀
    exact (hreg₂ q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₉ hq₁₀).trans
      (hreg₁ q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₉ hq₁₀)

end GraphMinor.Compute
