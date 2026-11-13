module

public import GraphMinor.Compute.GM06ClockwiseCuffMarkers
public import GraphMinor.Compute.GM06SelectRow
import GraphMinor.Compute.GM06SuccessorDegreeScan

/-!
# Loading a clockwise query from the ordinary instance arrays

The cuff index selects the given path row, whose first directed
edge is the path marker. The cuff vertex label then selects its
rotation row. Finally the two signed cuff labels are computed from
the edge count and cuff order. Thus the Reduction 1 query for
VI (5.7), page 133, reads only supplied structural data.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Load the path marker in 37, the signed cuff markers in 36 and
39, and the initial vertex's rotation in array 25. Index 295 is preserved. -/
def gm06LoadClockwiseRowProg : Cmd :=
  .seq (.assign 31 (.reg 295))
    (.seq (gm06SelectRowProg 8 24)
      (.seq (.assign 37 (.read 24 (.const 0)))
        (.seq (.assign 31 (.read 6 (.reg 295)))
          (.seq (gm06SelectRowProg 4 25) gm06ClockwiseCuffMarkersProg))))

/-- Loading a clockwise query returns precisely the supplied path
and vertex rotation, with all three marker labels computed from them. -/
theorem gm06LoadClockwiseRowProg_exec {w m : ℕ}
    (cs : List ℕ) (paths rots : List (List ℕ)) (i : ℕ)
    (hi : i < cs.length) (hip : i < paths.length) (hvertex : cs[i] < rots.length)
    (hne : 0 < paths[i].length) (s : State)
    (hw : 2 < 2 ^ w) (hsize : 2 * (m + cs.length) + 1 < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hrLen : (gm06EncodeRows rots).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows paths, v < 2 ^ w)
    (hrWords : ∀ v ∈ gm06EncodeRows rots, v < 2 ^ w)
    (h6 : s.arrs 6 = cs) (h8 : s.arrs 8 = gm06EncodeRows paths)
    (h4 : s.arrs 4 = gm06EncodeRows rots) (h12 : (s.arrs 12).length = m)
    (h295 : s.regs 295 = i) :
    ∃ s' t, Exec w gm06LoadClockwiseRowProg s s' t ∧
      t ≤ 59 + 17 * i + 17 * cs[i] + 22 * paths[i].length + 22 * rots[cs[i]].length ∧
      Keeps [7, 8, 9, 11, 31, 37, 296, 36, 39] [24, 25] s s' ∧
      s'.arrs 24 = paths[i] ∧ s'.arrs 25 = rots[cs[i]] ∧
      s'.regs 37 = paths[i][0] ∧ s'.regs 295 = i ∧
      s'.regs 36 = 2 * (m + gm06PreviousCuffIndex cs.length i) + 1 ∧
      s'.regs 39 = 2 * (m + i) := by
  let R := [7, 8, 9, 11, 31, 37, 296, 36, 39]
  let A := [24, 25]
  have hw1 : 1 < 2 ^ w := by omega
  have hiw : i < 2 ^ w := by omega
  have hrCount : rots.length < 2 ^ w := hrWords _ (by simp [gm06EncodeRows])
  have hvw : cs[i] < 2 ^ w := hvertex.trans hrCount
  have hfirst : paths[i][0] < 2 ^ w := hpWords _
    (gm06RowWord_mem_code (List.getElem_mem hip) (List.getElem_mem hne))
  let s₀ := s.setReg 31 i
  have he₀ : Exec w (.assign 31 (.reg 295)) s s₀ 2 := .assign (GraphMinor.Compute.Crossing.eval_reg h295 hiw)
  have hk₀ : Keeps R A s s₀ := (Keeps.refl R A s).setReg (by simp [R]) _
  obtain ⟨s₁, t₁, he₁, ht₁, hpath, _, _, hk₁⟩ := gm06SelectRowProg_exec
    8 24 (by decide) paths i hip s₀ hw1 (by simpa [s₀] using h8) hpLen hpWords (by simp [s₀])
  have hk₁' : Keeps R A s s₁ := hk₀.trans hk₁ (by simp [R]) (by simp [A])
  let s₂ := s₁.setReg 37 paths[i][0]
  have he₂ : Exec w (.assign 37 (.read 24 (.const 0))) s₁ s₂ 3 := by
    have hh := GraphMinor.Compute.Crossing.eval_read (a := 24) (s := s₁) (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (by simpa only [hpath] using hne) (by simpa only [hpath] using hfirst)
    simpa only [hpath, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 37) hh
  have hk₂ : Keeps R A s s₂ := hk₁'.setReg (by simp [R]) _
  have hcs₂ : s₂.arrs 6 = cs := (hk₂.2 6 (by simp [A])).trans h6
  let s₃ := s₂.setReg 31 cs[i]
  have he₃ : Exec w (.assign 31 (.read 6 (.reg 295))) s₂ s₃ 3 := by
    have hh := GraphMinor.Compute.Crossing.eval_read (a := 6) (s := s₂)
      (GraphMinor.Compute.Crossing.eval_reg ((hk₂.1 295 (by simp [R])).trans h295) hiw)
      (by simpa only [hcs₂] using hi)
      (by simpa only [hcs₂] using hvw)
    simpa only [hcs₂, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 31) hh
  have hk₃ : Keeps R A s s₃ := hk₂.setReg (by simp [R]) _
  obtain ⟨s₄, t₄, he₄, ht₄, hrot, _, _, hk₄⟩ := gm06SelectRowProg_exec
    4 25 (by decide) rots cs[i] hvertex s₃ hw1
      ((hk₃.2 4 (by simp [A])).trans h4) hrLen hrWords (by simp [s₃])
  have hk₄' : Keeps R A s s₄ := hk₃.trans hk₄ (by simp [R]) (by simp [A])
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, _, hp₅, hc₅⟩ := gm06ClockwiseCuffMarkersProg_exec s₄
    hi hw hsize
    (by rw [(hk₄'.2 6 (by simp [A])).trans h6])
    (by rw [hk₄'.2 12 (by simp [A])]; exact h12)
    ((hk₄'.1 295 (by simp [R])).trans h295)
  have hk : Keeps R A s s₅ := hk₄'.trans hk₅ (by simp [R]) (by simp [A])
  refine ⟨s₅, 2 + (t₁ + (3 + (3 + (t₄ + t₅)))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅)))), by omega, hk, ?_, ?_, ?_,
    (hk.1 295 (by simp [R])).trans h295, hp₅, hc₅⟩
  · exact (hk₅.2 24 (by simp)).trans ((hk₄.2 24 (by simp)).trans (by simpa [s₃, s₂] using hpath))
  · exact (hk₅.2 25 (by simp)).trans hrot
  · rw [hk₅.1 37 (by decide), hk₄.1 37 (by decide)]
    simp [s₃, s₂]

end GraphMinor.Compute
