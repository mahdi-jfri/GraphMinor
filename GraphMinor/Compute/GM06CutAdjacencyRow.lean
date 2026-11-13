module

public import GraphMinor.Compute.GM06CutNeighbourRowProgram

/-!
# CSR offsets for one computed cut adjacency row

The component searches of Section 9 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) use adjacency rows stored consecutively. This file records
the start cursor, appends the row computed from reverse origins, and records the end cursor. It also
defines the finite offset lists used by the full row loop.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths
open GraphMinor.Compute.Crossing

/-- Starting offsets for consecutive list rows. -/
def gm06CSRStarts : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | cursor, row :: rows => cursor :: gm06CSRStarts (cursor + row.length) rows

/-- Ending offsets for consecutive list rows. -/
def gm06CSREnds : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | cursor, row :: rows => (cursor + row.length) :: gm06CSREnds (cursor + row.length) rows

/-- One start offset is stored for each row. -/
theorem gm06CSRStarts_length (cursor : ℕ) (rows : List (List ℕ)) :
    (gm06CSRStarts cursor rows).length = rows.length := by
  induction rows generalizing cursor with
  | nil => rfl
  | cons row rows ih => simp only [gm06CSRStarts, List.length_cons, ih]

/-- One end offset is stored for each row. -/
theorem gm06CSREnds_length (cursor : ℕ) (rows : List (List ℕ)) :
    (gm06CSREnds cursor rows).length = rows.length := by
  induction rows generalizing cursor with
  | nil => rfl
  | cons row rows ih => simp only [gm06CSREnds, List.length_cons, ih]

/-- Neighbour rows for a suffix of copied vertex slots. -/
def gm06CutAdjacencyRowsFrom (n base : ℕ) (origins active live : List ℕ)
    (rows : List (List ℕ)) : List (List ℕ) :=
  (rows.zipIdx base).map (fun p => gm06CutRowNeighbours n origins active live p.2 p.1)

/-- Suffix vertex numbering advances by one at the next rotation. -/
theorem gm06CutAdjacencyRowsFrom_cons (n base : ℕ) (origins active live row : List ℕ)
    (rows : List (List ℕ)) :
    gm06CutAdjacencyRowsFrom n base origins active live (row :: rows) =
      gm06CutRowNeighbours n origins active live base row ::
        gm06CutAdjacencyRowsFrom n (base + 1) origins active live rows := by
  simp only [gm06CutAdjacencyRowsFrom, List.zipIdx_cons, List.map_cons]

/-- The adjacency pass emits one row per copied vertex slot. -/
theorem gm06CutAdjacencyRowsFrom_length (n base : ℕ) (origins active live : List ℕ)
    (rows : List (List ℕ)) :
    (gm06CutAdjacencyRowsFrom n base origins active live rows).length = rows.length := by
  simp only [gm06CutAdjacencyRowsFrom, List.length_map, List.length_zipIdx]

/-- Dense neighbour rows occupy at most one entry per vertex pair. -/
theorem gm06CutAdjacencyRowsFrom_flatten_length_le (n base : ℕ) (origins active live : List ℕ)
    (rows : List (List ℕ)) :
    (gm06CutAdjacencyRowsFrom n base origins active live rows).flatten.length ≤ n * rows.length := by
  induction rows generalizing base with
  | nil => simp [gm06CutAdjacencyRowsFrom]
  | cons row rows ih =>
    rw [gm06CutAdjacencyRowsFrom_cons, List.flatten_cons, List.length_append]
    have hr := gm06CutRowNeighbours_length_le n origins active live base row
    have ht := ih (base + 1)
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Record the CSR start and end around an actual adjacency-row append. -/
def gm06CutAdjacencyRowProg : Cmd :=
  .seq (.write 620 (.reg 666) (.reg 655))
    (.seq gm06CutNeighbourRowProg (.write 621 (.reg 666) (.reg 655)))

/-- Exact row and offset writes. Only the row's two header slots are
changed, and the entries buffer gains precisely the computed neighbours. -/
theorem gm06CutAdjacencyRowProg_exec {w n m u cap : ℕ}
    (origins active live row pre starts ends : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hm : 2 * m < 2 ^ w) (hu : u < n)
    (hl : row.length < 2 ^ w) (horgLen : origins.length = 2 * m)
    (hkeys : ∀ d ∈ row, d < 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hcap : n ≤ cap) (hfit : pre.length + cap + 2 < 2 ^ w)
    (h611 : s.arrs 611 = row) (h626 : s.arrs 626 = origins)
    (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h619 : s.arrs 619 = gm06IncidenceBits n live) (h618 : s.arrs 618 = List.range n)
    (h620 : s.regs 620 = n) (h666 : s.regs 666 = u)
    (hstart : s.arrs 620 = starts) (hend : s.arrs 621 = ends)
    (hstartLen : starts.length = n) (hendLen : ends.length = n)
    (hbuf : IsBuf 622 655 pre cap s) :
    ∃ sf t, Exec w gm06CutAdjacencyRowProg s sf t ∧ t ≤ 19 + 20 * n + 107 * row.length ∧
      Keeps [650, 651, 652, 653, 655] [614, 620, 621, 622] s sf ∧
      IsBuf 622 655 (pre ++ gm06CutRowNeighbours n origins active live u row)
        (cap - (gm06CutRowNeighbours n origins active live u row).length) sf ∧
      sf.arrs 620 = starts.set u pre.length ∧
      sf.arrs 621 = ends.set u (pre.length + (gm06CutRowNeighbours n origins active live u row).length) := by
  have hn : n < 2 ^ w := by omega
  let s₀ := s.writeArr 620 u pre.length
  have he₀ : Exec w (.write 620 (.reg 666) (.reg 655)) s s₀ 3 :=
    .write (eval_reg h666 (hu.trans hn)) (eval_reg hbuf.2 (by omega))
      (by simpa only [hstart, hstartLen] using hu)
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hb₁⟩ := gm06CutNeighbourRowProg_exec
    origins active live row pre s₀ hw hm hu hl horgLen hkeys hvalues hcap hfit
    (by simpa [s₀, State.writeArr] using h611) (by simpa [s₀, State.writeArr] using h626)
    (by simpa [s₀, State.writeArr] using h627) (by simpa [s₀, State.writeArr] using h619)
    (by simpa [s₀, State.writeArr] using h618) h620 h666
    ⟨by simpa [s₀, State.writeArr] using hbuf.1, hbuf.2⟩
  let sf := s₁.writeArr 621 u (pre.length + (gm06CutRowNeighbours n origins active live u row).length)
  have hout := gm06CutRowNeighbours_length_le n origins active live u row
  have he₂ : Exec w (.write 621 (.reg 666) (.reg 655)) s₁ sf 3 :=
    .write (eval_reg ((hk₁.1 666 (by decide)).trans h666) (hu.trans hn))
      (eval_reg (by simpa only [List.length_append] using hb₁.2) (by omega))
      (by rw [hk₁.2 621 (by decide)]; simpa [s₀, State.writeArr, hend, hendLen] using hu)
  have hk₀₁ : Keeps [650, 651, 652, 653, 655] [614, 620, 621, 622] s s₁ :=
    ((Keeps.refl _ _ s).writeArr (by simp) _ _).trans hk₁ (fun _ h => h) (by simp)
  refine ⟨sf, 3 + (t₁ + 3), .seq he₀ (.seq he₁ he₂), by omega,
    hk₀₁.writeArr (by simp) _ _, ?_, ?_, ?_⟩
  · exact ⟨by simpa [sf, State.writeArr] using hb₁.1, hb₁.2⟩
  · simpa only [sf, State.writeArr, State.setArr_arrs_ne _ _ (by decide : (620 : ℕ) ≠ 621),
      hk₁.2 620 (by decide), s₀, State.setArr_arrs_self, hstart]
  · simp only [sf, State.writeArr, State.setArr_arrs_self, hk₁.2 621 (by decide), s₀,
      State.setArr_arrs_ne _ _ (by decide : (621 : ℕ) ≠ 620), hend]

end GraphMinor.Compute
