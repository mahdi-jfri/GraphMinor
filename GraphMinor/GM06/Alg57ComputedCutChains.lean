module

public import GraphMinor.Compute.GM06CutPathMembership
public import GraphMinor.GM06.Alg57CutEquations

/-!
# Chaining the computed incoming and outgoing cut marks

The path ends in Section 9 of the implementation of VI (5.7),
page 133, are scattered from the same directed path words. A nonzero
incoming mark therefore has an outgoing partner at the other end of
that word, and conversely. Distinct vertex keys ensure that the
partner is not overwritten. This proves the path part of the fit
condition directly from the computed tables.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- Decoding preserves exactly the nonzero incoming path mark. -/
theorem computedCutPosition_incoming_iff (marks : GM06CutTables) (v a : ℕ) :
    (∃ p, gm06CutPositionAt marks v = some p ∧ cutIncoming p = some a) ↔
      marks.incoming[v]?.getD 0 = a + 1 := by
  simp only [cutIncoming_eq]
  unfold gm06CutPositionAt
  dsimp only
  split_ifs <;> simp_all <;> omega

/-- Decoding preserves exactly the nonzero outgoing path mark. -/
theorem computedCutPosition_outgoing_iff (marks : GM06CutTables) (v b : ℕ) :
    (∃ p, gm06CutPositionAt marks v = some p ∧ cutOutgoing p = some b) ↔
      marks.outgoing[v]?.getD 0 = b + 1 := by
  simp only [cutOutgoing_eq]
  unfold gm06CutPositionAt
  dsimp only
  split_ifs <;> simp_all <;> omega

/-- An incoming end in the computed tables is paired with the
outgoing end of the very same path word. -/
theorem computed_cut_incoming_chains {n m : ℕ} (origins : List ℕ)
    (paths : List (List ℕ)) (inner outer : List ℕ) (rows : List (List ℕ))
    (hrows : rows.length = n)
    (horg : ∀ d ∈ paths.flatten, origins[d]?.getD 0 < n)
    (hout : ((gm06CutPathEndPairs origins paths.flatten false).map Prod.fst).Nodup)
    {v : ℕ} {row : List ℕ} {p : GM06CutPosition} {a : ℕ}
    (hv : rows[v]? = some row)
    (hp : gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer) v = some p)
    (ha : cutIncoming p = some a) :
    ∃ u row' p', rows[u]? = some row' ∧
      gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer) u = some p' ∧
        cutOutgoing p' =
          some (gm06DartMate a) := by
  have hvn : v < n := by
    rw [← hrows]
    exact List.getElem?_eq_some_iff.mp hv |>.1
  have hmark := (computedCutPosition_incoming_iff _ v a).mp ⟨p, hp, ha⟩
  have hsource := gm06BuildCutTables_incoming_source origins paths inner outer hvn hmark
  let u := origins[gm06DartMate a]?.getD 0
  have hu : u < rows.length := hrows.symm ▸ horg _ hsource.1
  have houtmark := gm06BuildCutTables_outgoing_at (m := m) origins paths inner outer
    hsource.1 (horg _ hsource.1) hout
  obtain ⟨p', hp', ha'⟩ := (computedCutPosition_outgoing_iff _ u (gm06DartMate a)).mpr
    (by simpa only [Option.getD_some] using congrArg (fun q => q.getD 0) houtmark)
  exact ⟨u, rows[u], p', List.getElem?_eq_getElem hu, hp', ha'⟩

/-- An outgoing end in the computed tables is paired with the
reverse incoming end of the same word at its arrival vertex. -/
theorem computed_cut_outgoing_chains {n m : ℕ} (origins : List ℕ)
    (paths : List (List ℕ)) (inner outer : List ℕ) (rows : List (List ℕ))
    (hrows : rows.length = n)
    (horg : ∀ d ∈ paths.flatten, origins[gm06DartMate d]?.getD 0 < n)
    (hin : ((gm06CutPathEndPairs origins paths.flatten true).map Prod.fst).Nodup)
    {v : ℕ} {row : List ℕ} {p : GM06CutPosition} {b : ℕ}
    (hv : rows[v]? = some row)
    (hp : gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer) v = some p)
    (hb : cutOutgoing p = some b) :
    ∃ u row' p', rows[u]? = some row' ∧
      gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer) u = some p' ∧
        cutIncoming p' =
          some (gm06DartMate b) := by
  have hvn : v < n := by
    rw [← hrows]
    exact List.getElem?_eq_some_iff.mp hv |>.1
  have hmark := (computedCutPosition_outgoing_iff _ v b).mp ⟨p, hp, hb⟩
  have hsource := gm06BuildCutTables_outgoing_source origins paths inner outer hvn hmark
  let u := origins[gm06DartMate b]?.getD 0
  have hu : u < rows.length := hrows.symm ▸ horg _ hsource.1
  have hinmark := gm06BuildCutTables_incoming_at (m := m) origins paths inner outer
    hsource.1 (horg _ hsource.1) hin
  obtain ⟨p', hp', hb'⟩ := (computedCutPosition_incoming_iff _ u (gm06DartMate b)).mpr
    (by simpa only [Option.getD_some] using congrArg (fun q => q.getD 0) hinmark)
  exact ⟨u, rows[u], p', List.getElem?_eq_getElem hu, hp', hb'⟩

end GraphMinor.GM06
