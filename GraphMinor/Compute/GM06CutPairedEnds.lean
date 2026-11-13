module

public import GraphMinor.Compute.GM06CutCopiedEnds
public import GraphMinor.Compute.GM06CutDataBounds

/-!
# Global edge copies and reversal in the linkage cut

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) duplicates
every linkage edge and retains every other edge once. The computed mark
provenance identifies exactly which old ends receive the second tag.
Original row origins locate those marks at the right vertices.
Consequently reversing an active copied end always gives another
active copied end, including for loops with separated endpoints.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Exact copied-end criterion for the full computed rotations.
The row-origin and unique-end-key premises describe the original
finite graph and its vertex-disjoint directed linkage. -/
theorem gm06CutAlongLinkage_copies {n m d tag : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ) (rows : List (List ℕ))
    (hrows : rows.length = n) (ht : tag < 2)
    (hpath : ∀ d ∈ paths.flatten, d < 2 * m)
    (horgRows : ∀ pair ∈ rows.zipIdx, ∀ d ∈ pair.1, d < 2 * m → origins[d]?.getD 0 = pair.2)
    (hin : ((gm06CutPathEndPairs origins paths.flatten true).map Prod.fst).Nodup)
    (hout : ((gm06CutPathEndPairs origins paths.flatten false).map Prod.fst).Nodup) :
    gm06CutDart d tag ∈ (gm06CutAlongLinkageRotations n m origins paths inner outer rows).flatten ↔
      d ∈ rows.flatten ∧ (tag = 0 ∨ d ∈ paths.flatten ∨ gm06DartMate d ∈ paths.flatten) := by
  rw [gm06CutAlongLinkageRotations, gm06SplitRotationRows_cut_mem_iff _ _ ht]
  constructor
  · rintro ⟨pair, hp, hd, htag | ⟨p, hpos, hend⟩⟩
    · exact ⟨List.mem_flatten.mpr ⟨pair.1, List.fst_mem_of_mem_zipIdx hp, hd⟩, Or.inl htag⟩
    · have hv : pair.2 < n := by
        have h := List.snd_lt_add_of_mem_zipIdx hp
        simpa only [Nat.zero_add, hrows] using h
      have hdOrd : d < 2 * m := gm06CutPositionAt_pathEnds_bound origins paths inner outer hpath p hpos d hend
      have horg := horgRows pair hp d hd hdOrd
      have hlocal : ∃ p, gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer)
          (origins[d]?.getD 0) = some p ∧ d ∈ p.pathEnds := by rw [horg]; exact ⟨p, hpos, hend⟩
      have hmember := (gm06BuildCutTables_pathEnds_iff (m := m) origins paths inner outer (by omega) hin hout).mp hlocal
      exact ⟨List.mem_flatten.mpr ⟨pair.1, List.fst_mem_of_mem_zipIdx hp, hd⟩, Or.inr hmember⟩
  · rintro ⟨hd, htag | hmember⟩
    · obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
      obtain ⟨v, hv, heq⟩ := List.mem_iff_getElem.mp hr
      have hp : (row, v) ∈ rows.zipIdx := by
        apply List.mem_iff_getElem.mpr
        exact ⟨v, by simpa using hv, by simp only [List.getElem_zipIdx, Nat.zero_add, heq]⟩
      exact ⟨(row, v), hp, hd, Or.inl htag⟩
    · obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
      obtain ⟨v, hv, heq⟩ := List.mem_iff_getElem.mp hr
      have hp : (row, v) ∈ rows.zipIdx := by
        apply List.mem_iff_getElem.mpr
        exact ⟨v, by simpa using hv, by simp only [List.getElem_zipIdx, Nat.zero_add, heq]⟩
      have hdOrd : d < 2 * m := by
        rcases hmember with h | h
        · exact hpath d h
        · simpa only [gm06DartMate_involutive d] using gm06DartMate_lt (hpath _ h)
      have horg := horgRows (row, v) hp d hd hdOrd
      have hvn : origins[d]?.getD 0 < n := by rw [horg, ← hrows]; exact hv
      have hlocal := (gm06BuildCutTables_pathEnds_iff (m := m) origins paths inner outer hvn hin hout).mpr hmember
      rw [horg] at hlocal
      exact ⟨(row, v), hp, hd, Or.inr hlocal⟩

/-- Complete global reversal closure for the computed cut graph.
It uses only original paired ends, correct original origins, and the
simple directed-linkage end keys. No cut-side pairing is assumed. -/
theorem gm06CutDataOfLinkage_mate {n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (live : List ℕ)
    (hrows : rows.length = n) (hpath : ∀ d ∈ paths.flatten, d < 2 * m)
    (horgRows : ∀ pair ∈ rows.zipIdx, ∀ d ∈ pair.1, d < 2 * m → origins[d]?.getD 0 = pair.2)
    (hpair : ∀ d ∈ rows.flatten, gm06DartMate d ∈ rows.flatten)
    (hin : ((gm06CutPathEndPairs origins paths.flatten true).map Prod.fst).Nodup)
    (hout : ((gm06CutPathEndPairs origins paths.flatten false).map Prod.fst).Nodup) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    ∀ q ∈ data.activeDarts, gm06DartMate q ∈ data.activeDarts := by
  dsimp only
  intro q hq
  have hactive := (gm06CutDataOfLinkage_active_iff n m origins paths inner outer rows live q).mp hq
  let d := gm06UncutDart q
  let tag := (q / 2) % 2
  have ht : tag < 2 := Nat.mod_lt _ (by decide)
  have hrebuild : gm06CutDart d tag = q := gm06CutDart_rebuild q
  have hcopy : gm06CutDart d tag ∈ (gm06CutAlongLinkageRotations n m origins paths inner outer rows).flatten :=
    hrebuild.symm ▸ hactive.2
  have hclass := (gm06CutAlongLinkage_copies origins paths inner outer rows hrows ht hpath horgRows hin hout).mp hcopy
  have hclassMate : gm06DartMate d ∈ rows.flatten ∧
      (tag = 0 ∨ gm06DartMate d ∈ paths.flatten ∨ gm06DartMate (gm06DartMate d) ∈ paths.flatten) := by
    refine ⟨hpair d hclass.1, ?_⟩
    rcases hclass.2 with hz | hl | hr
    · exact Or.inl hz
    · exact Or.inr (Or.inr (by simpa only [gm06DartMate_involutive d] using hl))
    · exact Or.inr (Or.inl hr)
  have hmateCopy := (gm06CutAlongLinkage_copies origins paths inner outer rows hrows ht hpath horgRows hin hout).mpr hclassMate
  rw [gm06CutDart_mate, hrebuild] at hmateCopy
  apply (gm06CutDataOfLinkage_active_iff n m origins paths inner outer rows live (gm06DartMate q)).mpr
  refine ⟨?_, hmateCopy⟩
  have hq' : q < 2 * (2 * (m + inner.length + outer.length)) := by omega
  have hmate := gm06DartMate_lt hq'
  omega

end GraphMinor.Compute
