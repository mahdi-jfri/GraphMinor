module

public import GraphMinor.Compute.GM06Alg34DualHeader
public import GraphMinor.Compute.GM06Alg34DualEndsProg
public import GraphMinor.Compute.GM06Alg34DualRegionsProg

/-!
# Serializing the dual header, endpoints and regions

Join the three structural sections of the dual payload. The endpoint
scan and the transposed region scan read the prepared supplied-data
matrix and index arrays. Every earlier output word is retained, and
the exact unused capacity passes from one section to the next.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- The structural sections before the cuff and division data. -/
def gm06DualBodyWords (x : GM06DrawingData) (hR : 0 < x.regions.length) : List ℕ :=
  [x.regions.length, x.ends.length, x.n] ++
    gm06DualEndpointWords x hR (List.finRange x.ends.length) ++
    gm06DualRegionWords x (List.finRange x.n)

/-- Exact length of the three structural dual sections. -/
theorem gm06DualBodyWords_length (x : GM06DrawingData) (hR : 0 < x.regions.length) :
    (gm06DualBodyWords x hR).length =
      3 + 2 * x.ends.length + (gm06DualRegionWords x (List.finRange x.n)).length := by
  simp only [gm06DualBodyWords, List.length_append, List.length_cons, List.length_nil,
    gm06DualEndpointWords_length, List.length_finRange]

/-- Append the structural sections of the dual drawing. -/
def gm06DualBodyProg : Cmd :=
  .seq gm06DualHeaderProg (.seq gm06DualEndsProg gm06DualRegionsProg)

/-- The structural serializer appends its exact three sections with
quadratic incidence-scan work and retains all lower outer registers. -/
theorem gm06DualBodyProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (hR : 0 < x.regions.length) {pre : List ℕ} {s : State}
    (hw : 2 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hRspan : x.regions.length + 2 < 2 ^ w) (hEspan : x.ends.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length) (hr : s.regs 102 = x.regions.length)
    (hregions : s.arrs 52 = List.range x.regions.length) (hedges : s.arrs 51 = List.range x.ends.length)
    (hbuf : IsPrefixBuffer 55 pre ((gm06DualBodyWords x hR).length + cap) s)
    (hpos : s.regs 7804 = pre.length) (hfit : pre.length + (gm06DualBodyWords x hR).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualBodyProg s s' t ∧
      t ≤ 40 + (100 * (x.regions.length + 1) + 37) * x.ends.length +
        (200 * (x.regions.length + x.ends.length + 2) + 13) * x.n ∧
      IsPrefixBuffer 55 (pre ++ gm06DualBodyWords x hR) cap s' ∧
      s'.regs 7804 = (pre ++ gm06DualBodyWords x hR).length ∧
      (∀ A : ℕ, A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 7600 → s'.regs q = s.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hc := x.counts_le_size
  have hnN : x.n ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hmN : x.ends.length ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hrN : x.regions.length ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hbody := gm06DualBodyWords_length x hR
  let Rwords := gm06DualRegionWords x (List.finRange x.n)
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    gm06DualHeaderProg_exec hw1 (hnN.trans_lt hN) (hmN.trans_lt hN) (hrN.trans_lt hN)
      hn hm hr (cap := 2 * x.ends.length + Rwords.length + cap)
      (by have heq : (gm06DualBodyWords x hR).length + cap =
        3 + (2 * x.ends.length + Rwords.length + cap) := by change _ = 3 + (2 * x.ends.length + (gm06DualRegionWords x (List.finRange x.n)).length + cap); omega
          exact heq ▸ hbuf) hpos (by omega)
  have hb₁' : IsBuf 55 7804 (pre ++ [x.regions.length, x.ends.length, x.n])
      (2 * x.ends.length + Rwords.length + cap) s₁ := ⟨hb₁, hp₁⟩
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, ha₂, hg₂⟩ :=
    gm06DualEndsProg_exec x hR hw hN hsquare hRspan
      ((ha₁ 12 (by decide)).trans hmat) ((hg₁ 170 (by decide)).trans hstride)
      ((hg₁ 100 (by decide)).trans hn) ((hg₁ 101 (by decide)).trans hm)
      ((ha₁ 52 (by decide)).trans hregions) hb₁' (by omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hb₂' : IsPrefixBuffer 55
      ((pre ++ [x.regions.length, x.ends.length, x.n]) ++
        gm06DualEndpointWords x hR (List.finRange x.ends.length)) (Rwords.length + cap) s₂ := by
    have heq : (2 * x.ends.length + Rwords.length + cap) - 2 * x.ends.length = Rwords.length + cap := by omega
    exact heq ▸ hb₂.1
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, ha₃, hg₃⟩ :=
    gm06DualRegionsProg_exec x hw1 hN hsquare hRspan hEspan
      ((ha₂ 12 (by decide) (by decide)).trans ((ha₁ 12 (by decide)).trans hmat))
      ((hg₂ 170 (Or.inl (by decide)) (by decide)).trans ((hg₁ 170 (by decide)).trans hstride))
      ((hg₂ 100 (Or.inl (by decide)) (by decide)).trans ((hg₁ 100 (by decide)).trans hn))
      ((hg₂ 101 (Or.inl (by decide)) (by decide)).trans ((hg₁ 101 (by decide)).trans hm))
      ((ha₂ 52 (by decide) (by decide)).trans ((ha₁ 52 (by decide)).trans hregions))
      ((ha₂ 51 (by decide) (by decide)).trans ((ha₁ 51 (by decide)).trans hedges)) hb₂' hb₂.2
      (by simp only [List.length_append, List.length_cons, List.length_nil,
        gm06DualEndpointWords_length, List.length_finRange]; omega)
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), by omega, ?_, ?_, ?_, ?_⟩
  · simpa only [gm06DualBodyWords, List.append_assoc] using hb₃
  · simpa only [gm06DualBodyWords, List.append_assoc] using hp₃
  · intro A h54 h55 h56
    exact (ha₃ A h54 h55 h56).trans ((ha₂ A h54 h55).trans (ha₁ A h55))
  · intro q hq
    exact (hg₃ q hq).trans ((hg₂ q (Or.inl hq) (by omega)).trans (hg₁ q (by omega)))

end GraphMinor.Compute
