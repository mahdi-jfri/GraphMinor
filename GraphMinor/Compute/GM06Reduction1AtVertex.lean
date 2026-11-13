module

public import GraphMinor.Compute.GM06LoadClockwiseRow
public import GraphMinor.Compute.GM06DeleteCalibratedEdge
import GraphMinor.Compute.GM06SuccessorDegreeScan

/-!
# The Reduction 1 RAM query at a supplied cuff index

Load the given path's first end, the matching input rotation and
the computed signed cuff ends. Calibrate and scan the active edges,
then clear one qualifying edge. The execution bound includes both
row searches and the complete edge scan. This is the finite command
at one initial vertex in VI (5.7), page 133.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Try Reduction 1 at cuff index 295, reporting a deletion in 60. -/
def gm06Reduction1AtVertexProg : Cmd :=
  .seq gm06LoadClockwiseRowProg (gm06DeleteCalibratedEdgeProg 25 12)

/-- The query reads its three markers from structural arrays, then
excludes every finite candidate or deletes one with strict progress. -/
theorem gm06Reduction1AtVertexProg_exec {w : ℕ}
    (cs mask : List ℕ) (paths rots : List (List ℕ)) (i : ℕ)
    (hi : i < cs.length) (hip : i < paths.length) (hvertex : cs[i] < rots.length)
    (hne : 0 < paths[i].length) (s : State)
    (hw : 2 < 2 ^ w) (hsize : 2 * (mask.length + cs.length) + 1 < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hrLen : (gm06EncodeRows rots).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows paths, v < 2 ^ w)
    (hrWords : ∀ v ∈ gm06EncodeRows rots, v < 2 ^ w)
    (hbits : ∀ b ∈ mask, b ≤ 1) (hnd : rots[cs[i]].Nodup)
    (hp : 2 * (mask.length + gm06PreviousCuffIndex cs.length i) + 1 ∈ rots[cs[i]])
    (hq : paths[i][0] ∈ rots[cs[i]]) (hc : 2 * (mask.length + i) ∈ rots[cs[i]])
    (h6 : s.arrs 6 = cs) (h8 : s.arrs 8 = gm06EncodeRows paths)
    (h4 : s.arrs 4 = gm06EncodeRows rots) (h12 : s.arrs 12 = mask)
    (h295 : s.regs 295 = i) :
    let xs := rots[cs[i]]
    let p := 2 * (mask.length + gm06PreviousCuffIndex cs.length i) + 1
    let q := paths[i][0]
    let c := 2 * (mask.length + i)
    ∃ s' t, Exec w gm06Reduction1AtVertexProg s s' t ∧
      t ≤ 120 + 17 * i + 17 * cs[i] + 22 * paths[i].length +
        61 * xs.length + mask.length * (120 + 104 * xs.length) ∧
      Keeps [7, 8, 9, 11, 31, 37, 296, 36, 39, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60]
        [12, 24, 25] s s' ∧ s'.regs 295 = i ∧
      ((s'.regs 60 = 0 ∧ s'.arrs 12 = mask ∧ ∀ e (he : e < mask.length),
        ¬(mask[e] = 1 ∧ (gm06CalibratedSectorFlag xs p q c (2 * e) = 1 ∨
          gm06CalibratedSectorFlag xs p q c (2 * e + 1) = 1))) ∨
       (s'.regs 60 = 1 ∧ ∃ (e : ℕ) (he : e < mask.length),
        s'.regs 55 = e ∧ s'.arrs 12 = mask.set e 0 ∧ mask[e] = 1 ∧
        (gm06CalibratedSectorFlag xs p q c (2 * e) = 1 ∨
          gm06CalibratedSectorFlag xs p q c (2 * e + 1) = 1) ∧
        (s'.arrs 12).count 1 + 1 = mask.count 1)) := by
  dsimp only
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, _, hrow, hq₁, hi₁, hp₁, hc₁⟩ :=
    gm06LoadClockwiseRowProg_exec cs paths rots i hi hip hvertex hne s hw hsize
      hpLen hrLen hpWords hrWords h6 h8 h4 (by rw [h12]) h295
  have hrowBounds := gm06Row_word_bounds (List.getElem_mem hvertex) hrWords
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout⟩ := gm06DeleteCalibratedEdgeProg_exec
    25 12 rots[cs[i]] mask
      (2 * (mask.length + gm06PreviousCuffIndex cs.length i) + 1) paths[i][0]
      (2 * (mask.length + i)) s₁ hw hrowBounds.1 hrowBounds.2 hnd hp hq hc
      (by omega) hbits hrow ((hk₁.2 12 (by decide)).trans h12) hp₁ hq₁ hc₁
  let R := [7, 8, 9, 11, 31, 37, 296, 36, 39, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60]
  let A := [12, 24, 25]
  have hk₁' : Keeps R A s s₁ := hk₁.mono (by simp [R]) (by simp [A])
  have hframe : Keeps R A s s₂ := hk₁'.trans hk₂ (by simp [R]) (by simp [A])
  exact ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, hframe,
    (hk₂.1 295 (by decide)).trans hi₁, hout⟩

end GraphMinor.Compute
